-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch224
-- name    : Polychromatic418967fa_Branch224
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:25:40.507882+00:00
-- url     : https://prove2.me/theorems/62954be2-689d-4e80-9c46-26bdb2a7afd0
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch224_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_224 : allB 224 224 :=
  allB_succ' 2 223 224 (Eq.refl Bool.true) (allA_of_3_0 2 223 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  222 224 (Eq.refl Bool.true) (allA_succ_of_gcd 2 222 224 2 1 111 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 224 (accept_3_2 1 222 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 222 224))) (allB_succ' 4 221 224 (Eq.refl Bool.true) (allA_succ_of_accept 3 221 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 221 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 221 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 221 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 224 (accept_3_2 1 221 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 221 224)))) (allB_succ' 5 220 224 (Eq.refl Bool.true) (allA_of_3_0 5 220 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 219 224 (Eq.refl Bool.true) (allA_succ_of_accept 5 219 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 219 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 224 (accept_3_2 4 219 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 219 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 219 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 224 (accept_3_2 1 219 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 224)))))) (allB_succ' 7 218 224 (Eq.refl Bool.true) (allA_succ_of_gcd 6 218 224 2 3
  109 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 218 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 218 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 218 224 2 2 109 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 218 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 218 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 218 224 2 1 109 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 218 224 (accept_3_2 1 218 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 224))))))) (allB_succ' 8 217 224 (Eq.refl Bool.true) (allA_of_3_0 8 217
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 216 224 (Eq.refl Bool.true) (allA_succ_of_gcd 8 216 224 8 1
  27 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 224
  (accept_3_2 7 216 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 224 2 3 108 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 216 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 216 224 4 1 54 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 216 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 216 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 224 2 1 108 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 224 (accept_3_2 1 216 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 216 224))))))))) (allB_succ' 10 215 224 (Eq.refl Bool.true) (allA_succ_of_accept 9 215
  224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 215 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 215 224 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 215 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 224 (accept_3_2 7 215 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 215 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 215 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 224 (Polychromatic418967fa.accept_18_5_17_8_1_2984
  5 215 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 224 (accept_3_2 4
  215 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 215 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 215 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 224 (accept_3_2 1 215 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 215 224)))))))))) (allB_succ' 11 214 224 (Eq.refl Bool.true) (allA_of_3_0 11 214 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 213 224 (Eq.refl Bool.true) (allA_succ_of_accept 11 213 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 213 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 224 (accept_3_2 10 213 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 213 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 224 (Polychromatic418967fa.accept_13_8_5_3_1_427 8 213 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 224 (accept_3_2 7 213 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 213 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 224 (accept_3_2 4 213 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 213 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 213 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 224 (accept_3_2 1 213 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 224)))))))))))) (allB_succ' 13 212 224 (Eq.refl Bool.true) (allA_succ_of_gcd 12 212
  224 4 3 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  212 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 212 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 212 224 2 5 106 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 212 224 (Polychromatic418967fa.accept_19_9_3_15_1_2429 9 212 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 224 4 2 53 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 224 (accept_3_2 7 212 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 224 2 3 106 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693
  5 212 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 224 4 1 53 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 212 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 224 2 1 106 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 224 (accept_3_2 1 212 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  224))))))))))))) (allB_succ' 14 211 224 (Eq.refl Bool.true) (allA_of_3_0 14 211 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 210 224 (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 224 14 1 15 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 224 (accept_3_2 13 210 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 224 2 6 105 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 210 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 224 2 5 105 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 210 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 224 2 4 105 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 210 224 7 1 30 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 210 224 2 3 105 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 210 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 224 2 2 105 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 210 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 224 2 1 105 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 224 (accept_3_2 1 210 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 224))))))))))))))) (allB_succ' 16 209 224 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 209 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 209 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 209 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 224 (accept_3_2 13 209 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 224 (Polychromatic418967fa.accept_9_3_2_8_1_108
  12 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 224
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 224 (accept_3_2 10 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 209 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 224 (accept_3_2 7 209 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 209 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 224 (accept_3_2 4 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 209 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 209 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 224 (accept_3_2 1 209 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 224)))))))))))))))) (allB_succ' 17 208 224 (Eq.refl Bool.true) (allA_of_3_0 17 208
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 207 224 (Eq.refl Bool.true) (allA_succ_of_accept 17 207
  224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 224 (accept_3_2 16 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 224 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 224 (Polychromatic418967fa.accept_19_14_17_15_1_3761 14 207 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 224 (accept_3_2 13 207 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 207
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 224 (accept_3_2 10 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 224 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 224 (Polychromatic418967fa.accept_19_8_17_15_1_11952 8 207 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 224 (accept_3_2 7 207 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 207 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 224 (accept_3_2 4 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 207 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 207 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 224 (accept_3_2 1 207 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 224)))))))))))))))))) (allB_succ' 19 206 224 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 206 224 2 9 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 206 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 206 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 224 2 8 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  206 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 206 224 2 7 103 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 206 224 (accept_3_2 13
  206 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 206 224 2 6 103 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 206 224
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 206 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 206 224 2 5 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 206 224 (Polychromatic418967fa.accept_21_9_17_14_1_603 9 206 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 206 224 2 4 103 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 206 224 (accept_3_2 7 206 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 206 224 2 3 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 206 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 5
  206 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 224 2 2 103 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 224
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 3 206 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 224 2 1 103 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 224 (accept_3_2 1 206 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  224))))))))))))))))))) (allB_succ' 20 205 224 (Eq.refl Bool.true) (allA_of_3_0 20 205 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 204 224 (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 224 4 5 51 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 224 (accept_3_2 19 204 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 224 2 9 102 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 224
  (Polychromatic418967fa.accept_19_17_14_15_1_1403 17 204 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 204 224 4 4 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 204 224 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 204 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 224 2 7 102 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 224 (accept_3_2 13 204 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 224 4 3 51 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 204 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 224 2 5 102 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 224 (Polychromatic418967fa.accept_18_9_6_8_1_2989 9 204 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 224 4 2 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 224 (accept_3_2 7 204 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 224 2 3 102 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 204 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 224 4 1 51 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 204 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 224 2 1 102 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 224 (accept_3_2 1 204 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  224))))))))))))))))))))) (allB_succ' 22 203 224 (Eq.refl Bool.true) (allA_succ_of_gcd 21 203 224 7 3 29 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 203 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 224 (accept_3_2 19 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 203 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 224 (accept_3_2 16 203 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 203 224 7 2 29 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 203 224 (accept_3_2 13
  203 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 203 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 224 (accept_3_2 10 203 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 203 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 203 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 224
  (Polychromatic418967fa.accept_26_8_21_16_1_13379 8 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 203 224 7 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 203 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 203 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535
  5 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 224 (accept_3_2 4
  203 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 203 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 224 (accept_3_2 1 203 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 203 224)))))))))))))))))))))) (allB_succ' 23 202 224 (Eq.refl Bool.true) (allA_of_3_0 23 202 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 201 224 (Eq.refl Bool.true) (allA_succ_of_accept 23 201 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 224 (accept_3_2 22 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 224 (Polychromatic418967fa.accept_19_2_11_15_1_2404 21 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 224 (accept_3_2 19 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 201 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 224 (accept_3_2 16 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 224 (accept_3_2 13 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 201 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 224 (accept_3_2 10 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 224 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 224 (accept_3_2 7 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 201 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 224 (accept_3_2 4 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 224 (Polychromatic418967fa.accept_20_3_1_4_1_7654 3 201 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 224 (accept_3_2 1 201 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 224)))))))))))))))))))))))) (allB_succ' 25 200 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 200 224 8 3 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 200 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 200 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 224 2 11 100 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 21
  200 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 224 4 5 50 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 224 (accept_3_2 19
  200 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 224 2 9 100 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 224
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 200 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 200 224 8 2 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 200 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 200 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 224 2 7 100 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 224 (accept_3_2 13 200 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 224 4 3 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 200
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 224 2 5 100 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 224
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 200 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 224 8 1 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 200 224 (accept_3_2 7 200 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200
  224 2 3 100 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  200 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 200 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 200 224 4 1 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 200 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 200 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 224 2 1 100 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 224 (accept_3_2 1 200 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 200 224))))))))))))))))))))))))) (allB_succ' 26 199 224 (Eq.refl Bool.true)
  (allA_of_3_0 26 199 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 198 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 198 224 2 13 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 224 (accept_3_2 25 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 224 2 12 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 224 (Polychromatic418967fa.accept_19_4_8_15_1_585 23 198 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 224 2 11 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 224 2 10 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 224 (accept_3_2 19 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 224 2 9 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 198 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 224 2 8 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 224 2 7 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 224 (accept_3_2 13 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 224 2 6 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 198 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 224 2 5 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 224 2 4 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 224 (accept_3_2 7 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  224 2 3 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 224 (Polychromatic418967fa.accept_21_5_9_14_1_7247 5 198 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 224 2 2 99 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 198 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 224 2 1 99 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 224 (accept_3_2 1 198 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 224))))))))))))))))))))))))))) (allB_succ' 28 197 224 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 197 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 197 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 224 (Polychromatic418967fa.accept_12_2_5_8_1_159
  26 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 224 (accept_3_2 25
  197 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 224
  (Polychromatic418967fa.accept_13_11_2_3_1_883 24 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 197 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 197 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 224 (accept_3_2 22 197 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 197 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 224
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 224 (accept_3_2 19 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 224 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 224 (Polychromatic418967fa.accept_19_17_7_15_1_6418 17 197 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 224 (accept_3_2 16 197 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 197 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 224 (accept_3_2 13 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 197 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 224 (accept_3_2 10 197 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 224
  (Polychromatic418967fa.accept_19_8_7_15_1_13364 8 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 224 (accept_3_2 7 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 224 (Polychromatic418967fa.accept_21_6_8_14_1_10446 6 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 197 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 224 (accept_3_2 4 197 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 197 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 224 (accept_3_2 1 197 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  224)))))))))))))))))))))))))))) (allB_succ' 29 196 224 (Eq.refl Bool.true) (allA_of_3_0 29 196 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 195 224 (Eq.refl Bool.true) (allA_succ_of_accept 29 195 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 224 (accept_3_2 28 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 224 (Polychromatic418967fa.accept_23_4_11_17_1_13378 27 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 224 (accept_3_2 25 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 224 (Polychromatic418967fa.accept_21_3_6_14_1_5717 24 195
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 224 (accept_3_2 22 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 195 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 224 (accept_3_2 19 195 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 224 (accept_3_2 16 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 224 (Polychromatic418967fa.accept_22_15_19_4_1_10263 15 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 224 (accept_3_2 13 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 195 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 224 (accept_3_2 10 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 224 (Polychromatic418967fa.accept_21_8_6_14_1_4184 8 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 224 (accept_3_2 7 195 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 195 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 224 (accept_3_2 4 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 195 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 224 (accept_3_2 1 195 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 224)))))))))))))))))))))))))))))) (allB_succ' 31 194 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 194 224 2 15 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 194 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 224 2 14 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 224
  (Polychromatic418967fa.accept_17_10_7_3_1_727 27 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 224 2 13 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 224 (accept_3_2 25 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 224 2 12 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 194 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 224 2 11 97 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 224 2 10 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 224 (accept_3_2 19 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 224 2 9 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 194 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 224 2 8 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 224 2 7 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 224 (accept_3_2 13 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 224 2 6 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 194 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 224 2 5 97 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 224
  (Polychromatic418967fa.accept_13_9_12_3_1_907 9 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 224 2 4 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 224 (accept_3_2 7 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  224 2 3 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 194 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 224 2 2 97 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 194 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 224 2 1 97 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 224 (accept_3_2 1 194 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 224))))))))))))))))))))))))))))))) (allB_succ' 32 193 224
  (Eq.refl Bool.true) (allA_of_3_0 32 193 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 192 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 192 224 32 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 192 224 (accept_3_2 31 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 224 2 15 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 192 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 224 4 7 48 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 192 224 2 13 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 224 (accept_3_2 25 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 224 8 3 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 192 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 224 2 11 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 224 (Polychromatic418967fa.accept_11_10_5_4_1_711
  21 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 224 4 5 48 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 224
  (accept_3_2 19 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 224 2 9 96 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 224 16 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 192 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 192 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 224 2 7 96 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 224 (accept_3_2 13 192 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 224 4 3 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11
  192 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 224 2 5 96 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 224
  (Polychromatic418967fa.accept_15_9_12_14_1_963 9 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 224 8 1 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 224 (accept_3_2 7 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  224 2 3 96 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 192 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 224 4 1 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 192 224 (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 192 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 224 2 1 96 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 224 (accept_3_2 1 192 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 224))))))))))))))))))))))))))))))))) (allB_succ' 34 191 224 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 191 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 224 (Polychromatic418967fa.accept_9_5_2_8_1_109
  32 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 224 (accept_3_2 31
  191 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 30 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 191 224 (Polychromatic418967fa.accept_21_8_2_14_1_10496 29 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 224 (accept_3_2 28 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 224 (accept_3_2 25 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 224 (accept_3_2 22 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 224
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 224 (accept_3_2 19 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 224 (accept_3_2 16 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 224 (accept_3_2 13 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 224 (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 224 (accept_3_2 10 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 191 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 224
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 224 (accept_3_2 7 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 224 (accept_3_2 4 191 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 224 (accept_3_2 1 191 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  224)))))))))))))))))))))))))))))))))) (allB_succ' 35 190 224 (Eq.refl Bool.true) (allA_of_3_0 35 190 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 189 224 (Eq.refl Bool.true) (allA_succ_of_gcd 35 189 224 7 5 27 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 189 224
  (accept_3_2 34 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 224
  (Polychromatic418967fa.accept_10_3_9_4_1_960 33 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 189 224 (Polychromatic418967fa.accept_25_7_14_24_1_13377 32 189 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 224 (accept_3_2 31 189 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 189 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 189 224 7 4 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 189 224 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 189 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 224 (Polychromatic418967fa.accept_19_7_18_15_1_5061 26 189
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 224 (accept_3_2 25 189
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 224
  (Polychromatic418967fa.accept_13_11_7_3_1_894 24 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 189 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 224 (accept_3_2 22 189 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 189 224 7 3 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 189 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 20 189 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 224 (accept_3_2 19 189 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 189
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 224 (accept_3_2 16 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 189 224 7 2 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 189 224 (accept_3_2 13 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 189 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 189 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 224 (accept_3_2 10
  189 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 224
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 189 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 189 224 7 1 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 189 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 189 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 224 (accept_3_2 4 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 189 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 224 (Polychromatic418967fa.accept_19_2_18_15_1_6413 2 189 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 224 (accept_3_2 1 189 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 224)))))))))))))))))))))))))))))))))))) (allB_succ' 37 188 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 36 188 224 4 9 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 188 224 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 188 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 224 2 17 94 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 224
  (Polychromatic418967fa.accept_19_14_17_15_1_3761 33 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 188 224 4 8 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 188 224 (accept_3_2 31 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 224 2 15 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 188 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 224 4 7 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 224
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 224 2 13 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 224 (accept_3_2 25 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 224 4 6 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 188 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 188 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 224 2 11 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575
  21 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 224 4 5 47 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 224
  (accept_3_2 19 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 224 2 9 94 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 224
  (Polychromatic418967fa.accept_21_17_20_14_1_11808 17 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 188 224 4 4 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 188 224 (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 188 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 224 2 7 94 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 224 (accept_3_2 13 188 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 224 4 3 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 224
  (Polychromatic418967fa.accept_21_11_20_14_1_4179 11 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 188 224 2 5 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 188 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 188 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 224 4 2 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 224 (accept_3_2 7 188 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 224 2 3 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 5
  188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 188 224 4 1 47 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 188 224
  (Polychromatic418967fa.accept_19_3_17_15_1_6459 3 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 188 224 2 1 94 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 188 224 (accept_3_2 1 188 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  224))))))))))))))))))))))))))))))))))))) (allB_succ' 38 187 224 (Eq.refl Bool.true) (allA_of_3_0 38 187 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 186 224 (Eq.refl Bool.true) (allA_succ_of_gcd 38 186 224 2 19 93 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 224
  (accept_3_2 37 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 186 224 2 18 93 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 186 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 224 2 17 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 186 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 224 2 16 93 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 224 (accept_3_2 31 186 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 186 224 2 15 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 186 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29
  186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 224 2 14 93 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 224
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 224 2 13 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 224 (accept_3_2 25 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 224 2 12 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 186 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 224 2 11 93 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 224 2 10 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 224 (accept_3_2 19 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 224 2 9 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 224 (Polychromatic418967fa.accept_21_17_18_14_1_4138 17 186 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 224 2 8 93 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 224 2 7 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 224 (accept_3_2 13 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 224 2 6 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 224 2 5 93 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 224 2 4 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 224 (accept_3_2 7 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  224 2 3 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 186 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 224 2 2 93 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 186 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 224 2 1 93 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 224 (accept_3_2 1 186 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 224))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 185
  224 (Eq.refl Bool.true) (allA_succ_of_accept 39 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 224 (accept_3_2 37 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 224 (accept_3_2 34 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 224
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 224 (accept_3_2 31 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 185 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 224 (accept_3_2 28 185 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 224 (accept_3_2 25 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 224 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 224 (accept_3_2 22 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 224 (accept_3_2 19 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 224 (Polychromatic418967fa.accept_17_1_15_3_1_1501 18 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 224 (accept_3_2 16 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 185 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 224 (accept_3_2 13 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 185 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 224 (accept_3_2 10 185 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 224 (accept_3_2 7 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 224 (Polychromatic418967fa.accept_21_5_17_14_1_4178 5 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 224 (accept_3_2 4 185 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 224 (accept_3_2 1 185 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  224)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 184 224 (Eq.refl Bool.true) (allA_of_3_0 41 184 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 183 224 (Eq.refl Bool.true) (allA_succ_of_accept 41 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 224 (accept_3_2 40 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 183 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 224 (accept_3_2 37 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 183 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 224 (accept_3_2 34 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 224 (accept_3_2 31 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 183 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 224 (accept_3_2 28 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 183 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 224 (accept_3_2 25 183 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 183 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 224 (accept_3_2 22 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 224 (Polychromatic418967fa.accept_17_4_13_3_1_7166 21 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 224 (accept_3_2 19 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 183 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 224 (accept_3_2 16 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 224 (accept_3_2 13 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 183 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 224 (accept_3_2 10 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 224 (accept_3_2 7 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 183 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 224 (accept_3_2 4 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 3 183 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 224 (accept_3_2 1 183 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 224)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 182 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 182 224 14 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 182 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 182 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 224 2 20 91 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 224 2 19 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 224 (accept_3_2 37 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 224 2 18 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 182 224 7 5 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 182 224 2 17 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 182 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 182 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 224 2 16 91 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 224 (accept_3_2 31 182 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 224 2 15 91 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 224
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 182 224 14 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 182 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 182 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 182 224 2 13 91 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 182 224 (accept_3_2 25 182 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 182 224 2 12 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 182 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23
  182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 224 2 11 91 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 182 224 7 3 26 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 182 224 2 10 91 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 224
  (accept_3_2 19 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 182 224 2 9 91 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 182 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 182 224 2 8 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 182 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 182 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 182 224 14 1 13 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 182 224 (accept_3_2 13 182 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 182 224 2 6 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 182 224 (Polychromatic418967fa.accept_12_11_2_8_1_511
  11 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 224 2 5 91 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 224
  (Polychromatic418967fa.accept_19_9_11_15_1_6406 9 182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 224 2 4 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 182 224 7 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 182 224 2 3 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 182 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 182 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 224 2 2 91 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  182 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 224 2 1 91 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 224 (accept_3_2 1
  182 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 224)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 181 224 (Eq.refl Bool.true) (allA_of_3_0 44 181 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 180 224 (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 224 4 11 45 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 224 (accept_3_2 43 180 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 180 224 2 21 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 180 224 (Polychromatic418967fa.accept_13_2_11_3_1_873
  41 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 224 4 10 45 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 224
  (Polychromatic418967fa.accept_21_18_12_14_1_11842 39 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 180 224 2 19 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 180 224 (accept_3_2 37 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 224 4 9 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 224 (Polychromatic418967fa.accept_24_11_12_8_1_13376 35 180 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 224 2 17 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 224
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 180 224 4 8 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 180 224 (accept_3_2 31 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  180 224 2 15 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 224 (Polychromatic418967fa.accept_19_10_9_15_1_11965 29 180 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 224 4 7 45 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 224
  (Polychromatic418967fa.accept_13_1_11_3_1_901 27 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 224 2 13 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 224 (accept_3_2 25 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 224 4 6 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 180 224 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 180 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 224 2 11 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 224
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 21 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 224 4 5 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 180 224 (accept_3_2 19 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  180 224 2 9 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 224 (Polychromatic418967fa.accept_24_17_12_8_1_2990 17 180 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 224 4 4 45 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 224
  (Polychromatic418967fa.accept_13_2_11_3_1_873 15 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 180 224 2 7 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 180 224 (accept_3_2 13 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 224 4 3 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 180 224 (Polychromatic418967fa.accept_17_11_10_3_1_2364 11 180 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 224 2 5 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 224
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 224 4 2 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 224 (accept_3_2 7 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180
  224 2 3 90 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  180 224 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 180 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 180 224 4 1 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 180 224 (Polychromatic418967fa.accept_19_3_9_15_1_9240 3 180 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 224 2 1 90 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 224 (accept_3_2 1 180 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 224))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 179 224
  (Eq.refl Bool.true) (allA_succ_of_accept 45 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 224
  (Polychromatic418967fa.accept_17_10_9_3_1_7144 44 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 224 (accept_3_2 43 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 224 (Polychromatic418967fa.accept_19_4_8_15_1_585 42 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 224 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 224 (accept_3_2 40 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 224 (accept_3_2 37 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 224 (Polychromatic418967fa.accept_19_17_8_15_1_6448 36 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 224 (accept_3_2 34 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 179 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 224
  (Polychromatic418967fa.accept_13_6_10_3_1_897 32 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 224 (accept_3_2 31 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 224 (Polychromatic418967fa.accept_25_5_4_24_1_13375 30 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 224 (accept_3_2 28 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 224 (accept_3_2 25 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 224 (accept_3_2 22 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 179 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 224
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 224 (accept_3_2 19 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 224 (Polychromatic418967fa.accept_19_17_8_15_1_6448 17 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 224 (accept_3_2 16 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 224 (accept_3_2 13 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 224 (Polychromatic418967fa.accept_19_12_8_15_1_5067 12 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 224 (accept_3_2 10 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 224 (accept_3_2 7 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 224 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 179 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 224 (accept_3_2 4 179 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 224 (accept_3_2 1 179 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  224)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 178 224 (Eq.refl Bool.true) (allA_of_3_0 47 178 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 177 224 (Eq.refl Bool.true) (allA_succ_of_accept 47 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 224 (accept_3_2 46 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 224 (Polychromatic418967fa.accept_21_3_9_14_1_5701 45 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 224 (accept_3_2 43 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 177
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 224 (accept_3_2 40 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 224 (accept_3_2 37 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 224 (Polychromatic418967fa.accept_21_15_9_14_1_10462 36 177 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 224 (accept_3_2 34 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 224 (accept_3_2 31 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 224 (accept_3_2 28 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 224 (Polychromatic418967fa.accept_17_10_7_3_1_727 27 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 224 (accept_3_2 25 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 224 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 177
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 224 (accept_3_2 22 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 224 (accept_3_2 19 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 224 (accept_3_2 16 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 224 (Polychromatic418967fa.accept_21_15_9_14_1_10462 15 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 224 (accept_3_2 13 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 177 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 224 (accept_3_2 10 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 224 (accept_3_2 7 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 177 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 224 (accept_3_2 4 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 177 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 224 (accept_3_2 1 177 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 224)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 176 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 176 224 16 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 176 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 176 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 224 2 23 88 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 224 4 11 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 224 (accept_3_2 43 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 224 2 21 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 224 (Polychromatic418967fa.accept_18_5_14_8_1_2966 41 176 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 224 8 5 22 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 224 2 19 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 224 (accept_3_2 37 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 224 4 9 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 176 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 224 2 17 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 224 16 2 11 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 224 (accept_3_2 31
  176 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 224 2 15 88 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 176 224 4 7 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 176 224 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 176 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 224 2 13 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 224 (accept_3_2 25 176 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 224 8 3 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 176
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 224 2 11 88 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 224 4 5 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 176 224 (accept_3_2 19 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  176 224 2 9 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 176 224 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 176 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 224 16 1 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 224 2 7 88 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 224 (accept_3_2 13
  176 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 224 4 3 44 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 176 224 2 5 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 176 224 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 176 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 224 8 1 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 224 (accept_3_2 7 176 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 224 2 3 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 176 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 224 4 1 44 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 224 2 1 88 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 224 (accept_3_2 1 176 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  224))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 175 224 (Eq.refl Bool.true) (allA_of_3_0 50 175
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 174 224 (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 224 2
  25 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174
  224 (accept_3_2 49 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 174 224 2 24 87 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 174 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 174 224 2 23 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 174 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 224 2 22 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 224 (accept_3_2 43 174 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 174 224 2 21 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 174 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 41
  174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 224 2 20 87 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 224 2 19 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 224 (accept_3_2 37 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 224 2 18 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 35 174 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 224 2 17 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 224 2 16 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 224 (accept_3_2 31 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 224 2 15 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 174 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 224 2 14 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 224 2 13 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 224 (accept_3_2 25 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 224 2 12 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 174 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 224 2 11 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 224 2 10 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 224 (accept_3_2 19 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 224 2 9 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 224 (Polychromatic418967fa.accept_19_17_3_15_1_9284 17 174 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 224 2 8 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 224 2 7 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 224 (accept_3_2 13 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 224 2 6 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 174 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 224 2 5 87 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 224 2 4 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 224 (accept_3_2 7 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  224 2 3 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 174 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 224 2 2 87 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 174 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 224 2 1 87 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 224 (accept_3_2 1 174 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 224)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 173 224 (Eq.refl Bool.true) (allA_succ_of_accept 51 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 224 (accept_3_2 49 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 47 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 224 (accept_3_2 46 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 224
  (Polychromatic418967fa.accept_19_6_2_15_1_9266 44 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 224 (accept_3_2 43 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 173 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 224 (accept_3_2 40 173 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 224 (accept_3_2 37 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 224 (accept_3_2 34 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 224 (accept_3_2 31 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 224 (accept_3_2 28 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 173 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 224 (accept_3_2 25 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 173 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 224 (accept_3_2 22 173 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 224
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 224 (accept_3_2 19 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 224 (accept_3_2 16 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 224 (accept_3_2 13 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 224 (Polychromatic418967fa.accept_19_11_2_15_1_5062 11 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 224 (accept_3_2 10 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 224
  (Polychromatic418967fa.accept_19_8_2_15_1_2426 8 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 224 (accept_3_2 7 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 224 (accept_3_2 4 173 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 224 (accept_3_2 1 173 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  224)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 172 224 (Eq.refl Bool.true) (allA_of_3_0 53 172
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 171 224 (Eq.refl Bool.true) (allA_succ_of_accept 53 171
  224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 224 (accept_3_2 52 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 224 (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 171 224 (Polychromatic418967fa.accept_13_11_2_3_1_883 50 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 224 (accept_3_2 49 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 224 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 224 (accept_3_2 46 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 224 (Polychromatic418967fa.accept_13_5_2_3_1_1526 44 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 224 (accept_3_2 43 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 224 (accept_3_2 40 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 224 (Polychromatic418967fa.accept_13_12_2_3_1_1527 38 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 224 (accept_3_2 37 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 224 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 224 (accept_3_2 34 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 224 (Polychromatic418967fa.accept_20_13_11_4_1_2042 33 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 224 (Polychromatic418967fa.accept_17_15_1_3_1_1488 32 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 224 (accept_3_2 31 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 224 (accept_3_2 28 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 224 (Polychromatic418967fa.accept_17_9_1_3_1_4626 26 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 224 (accept_3_2 25 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 24 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 224 (accept_3_2 22 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 21 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 224 (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 224 (accept_3_2 19 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 224 (accept_3_2 16 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 224 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 224 (accept_3_2 13 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 224 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 171
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 224 (accept_3_2 10 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 224 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 8 171 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 224 (accept_3_2 7 171 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 171 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 224 (accept_3_2 4 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 171 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 2 171 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 224 (accept_3_2 1 171 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 224)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 170 224
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 170 224 2 27 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 170 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 224 2 26 85 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 224
  (Polychromatic418967fa.accept_15_6_5_14_1_429 51 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 224 2 25 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 224 (accept_3_2 49 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 224 2 24 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 170 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 224 2 23 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 224
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 224 2 22 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 224 (accept_3_2 43 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 224 2 21 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 170 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 224 2 20 85 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 224
  (Polychromatic418967fa.accept_15_9_5_14_1_973 39 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 224 2 19 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 224 (accept_3_2 37 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 224 2 18 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 170 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 224 2 17 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 224
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 224 2 16 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 224 (accept_3_2 31 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 224 2 15 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 170 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 224 2 14 85 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 224
  (Polychromatic418967fa.accept_21_6_2_14_1_5688 27 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 224 2 13 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 224 (accept_3_2 25 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 224 2 12 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 170 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 224 2 11 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 224
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 224 2 10 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 224 (accept_3_2 19 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 224 2 9 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 170 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 224 2 8 85 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 224
  (Polychromatic418967fa.accept_13_2_1_3_1_419 15 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 224 2 7 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 224 (accept_3_2 13 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 224 2 6 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 170 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 224 2 5 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 224
  (Polychromatic418967fa.accept_15_9_5_14_1_973 9 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 224 2 4 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 224 (accept_3_2 7 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  224 2 3 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 170 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 224 2 2 85 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 224 (Polychromatic418967fa.accept_19_3_18_15_1_3711 3 170 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 224 2 1 85 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 224 (accept_3_2 1 170 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 169 224 (Eq.refl Bool.true) (allA_of_3_0 56 169 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 168 224 (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 224 56 1 3 4 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 224 (accept_3_2 55 168 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 168 224 2 27 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 168 224
  (Polychromatic418967fa.accept_25_3_18_24_1_13374 53 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 168 224 4 13 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 168 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 168 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 224 2 25 84 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 168 224 7 7 24 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 168 224 8 6 21 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 168 224 2 23 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 168 224 (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 168 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 224 4 11 42 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 224 (accept_3_2 43 168 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 224 14 3 12 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 224 8 5 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 168 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 168 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 224 2 19 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 224 (accept_3_2 37 168 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 224 4 9 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 168 224 7 5 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 168 224 2 17 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 224
  (Polychromatic418967fa.accept_23_10_7_17_1_10035 33 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 168 224 8 4 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 224 (accept_3_2 31 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 224 2 15 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 224 28 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 224 (Polychromatic418967fa.accept_18_9_6_8_1_2989
  27 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 224 2 13 84 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 224
  (accept_3_2 25 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 224 8 3 21 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 224 2 11 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 168 224 7 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 168 224 4 5 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 224 (accept_3_2 19 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 224 2 9 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 224 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 168 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 224 8 2 21 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 224
  (Polychromatic418967fa.accept_13_2_12_3_1_415 15 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 168 224 14 1 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 168 224 (accept_3_2 13 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 224 4 3 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 224 2 5 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9
  168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 224 8 1 21 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 168 224 7 1 24 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 168 224 2 3 84 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 224 4 1 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 168 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 224 2 1 84 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 224 (accept_3_2 1 168 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 167 224
  (Eq.refl Bool.true) (allA_succ_of_accept 57 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 224 (accept_3_2 55 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 224 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 224 (accept_3_2 52 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 224
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 50 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 224 (accept_3_2 49 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 224 (accept_3_2 46 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 224
  (Polychromatic418967fa.accept_13_5_11_3_1_902 44 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 224 (accept_3_2 43 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 41 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 224 (accept_3_2 40 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 224 (accept_3_2 37 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 224 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 224 (accept_3_2 34 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 167 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 224 (accept_3_2 31 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 224 (accept_3_2 28 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 224 (accept_3_2 25 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 224 (accept_3_2 22 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 224 (accept_3_2 19 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 224 (Polychromatic418967fa.accept_13_5_11_3_1_902 18 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 224 (accept_3_2 16 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 224 (accept_3_2 13 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 224 (accept_3_2 10 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 224
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 224 (accept_3_2 7 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 224 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 224 (accept_3_2 4 167 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 224 (accept_3_2 1 167 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 166 224 (Eq.refl Bool.true) (allA_of_3_0
  59 166 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 165 224 (Eq.refl Bool.true) (allA_succ_of_accept 59
  165 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 165 224 (accept_3_2 58 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 165 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 165 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 165 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 224 (accept_3_2 55 165 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 224 (Polychromatic418967fa.accept_12_6_9_8_1_165
  54 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 224 (accept_3_2 52 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 224 (accept_3_2 49 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 224 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 165 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 224 (accept_3_2 46 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 45 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 44 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 224 (accept_3_2 43 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 165 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 224 (accept_3_2 40 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 224 (accept_3_2 37 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 224 (accept_3_2 34 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 224 (accept_3_2 31 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 224 (accept_3_2 28 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 224 (Polychromatic418967fa.accept_18_9_3_8_1_5419 27 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 224 (accept_3_2 25 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 165 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 224 (accept_3_2 22 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 224 (accept_3_2 19 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 224 (accept_3_2 16 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 224 (accept_3_2 13 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 224 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 165 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 224 (accept_3_2 10 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 224 (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 224 (accept_3_2 7 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 165 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 224 (accept_3_2 4 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 224 (Polychromatic418967fa.accept_25_3_15_24_1_13373 3 165 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 224 (accept_3_2 1 165 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 164
  224 (Eq.refl Bool.true) (allA_succ_of_gcd 60 164 224 4 15 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 164 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 164 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 224 2 29 82 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 224 4 14 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 224 (accept_3_2 55 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 224 2 27 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 224 (Polychromatic418967fa.accept_17_2_11_3_1_4654 53 164 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 224 4 13 41 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 224 2 25 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 224 (accept_3_2 49 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 224 4 12 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 224 (Polychromatic418967fa.accept_21_5_17_14_1_4178 47 164 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 224 2 23 82 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 224
  (Polychromatic418967fa.accept_19_7_12_15_1_13329 45 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 164 224 4 11 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 164 224 (accept_3_2 43 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 224 2 21 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 164 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 224 4 10 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 224 2 19 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 224 (accept_3_2 37 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 224 4 9 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 164 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 224 2 17 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 33
  164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 224 4 8 41 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 224 (accept_3_2 31
  164 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 224 2 15 82 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 224
  (Polychromatic418967fa.accept_21_8_17_14_1_4156 29 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 164 224 4 7 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 164 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 164 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 224 2 13 82 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 224 (accept_3_2 25 164 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 224 4 6 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 164 224 2 11 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 164 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 164 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 224 4 5 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 224 (accept_3_2 19 164 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 224 2 9 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 224 (Polychromatic418967fa.accept_18_17_2_8_1_6800
  17 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 224 4 4 41 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 224 2 7 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 224 (accept_3_2 13 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 224 4 3 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 164 224 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 164 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 224 2 5 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9
  164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 224 4 2 41 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 224 (accept_3_2 7
  164 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 224 2 3 82 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 164 224 4 1 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 164 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 164 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 224 2 1 82 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 224 (accept_3_2 1 164 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 163
  224 (Eq.refl Bool.true) (allA_of_3_0 62 163 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 162 224
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 224 2 31 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 224 (accept_3_2 61 162 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 162 224 2 30 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 162 224 (Polychromatic418967fa.accept_20_19_2_4_1_2057 59 162 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 224 2 29 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 224 2 28 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 224 (accept_3_2 55 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 224 2 27 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 224 (Polychromatic418967fa.accept_13_1_6_3_1_1547 53 162 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 224 2 26 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 224
  (Polychromatic418967fa.accept_11_7_8_4_1_718 51 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 224 2 25 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 224 (accept_3_2 49 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 224 2 24 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 162 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 224 2 23 81 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 224
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 224 2 22 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 224 (accept_3_2 43 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 224 2 21 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 41 162 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 224 2 20 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 224 2 19 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 224 (accept_3_2 37 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 224 2 18 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 224 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 162 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 224 2 17 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 224 2 16 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 224 (accept_3_2 31 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 224 2 15 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 29 162 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 224 2 14 81 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 224 2 13 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 224 (accept_3_2 25 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 224 2 12 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 162 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 224 2 11 81 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 224 2 10 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 224 (accept_3_2 19 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 224 2 9 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 162 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 224 2 8 81 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 224 2 7 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 224 (accept_3_2 13 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 224 2 6 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 162 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 224 2 5 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 224 2 4 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 224 (accept_3_2 7 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  224 2 3 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 224 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 162 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 224 2 2 81 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 162 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 224 2 1 81 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 224 (accept_3_2 1 162 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 161 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 161 224 7 9 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 161 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 224 (accept_3_2 61 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 161 224 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 59 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 161 224 (accept_3_2 58 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 161 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 161 224 7 8 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 161 224 (accept_3_2 55 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 161 224 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 224 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 161
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 224 (accept_3_2 52 161
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 161 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 161 224 7 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 161 224 (Polychromatic418967fa.accept_13_9_5_3_1_428
  48 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 224
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 224 (accept_3_2 46 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 224 (Polychromatic418967fa.accept_19_6_9_15_1_3694 44 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 224 (accept_3_2 43 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 161 224 7 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 161 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011
  41 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 224 (accept_3_2 40
  161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 161 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 224 (accept_3_2 37 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 161 224 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 161 224 7 5 23 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 161 224 (accept_3_2 34 161 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 224
  (Polychromatic418967fa.accept_13_6_5_3_1_426 32 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 224 (accept_3_2 31 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 224 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 224 (Polychromatic418967fa.accept_17_12_8_3_1_4646 29 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 161 224 7 4 23 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 161 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 161 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 224 (accept_3_2 25 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 161 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 224 (accept_3_2 22 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  161 224 7 3 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 161 224 (Polychromatic418967fa.accept_18_2_17_8_1_1893 20 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 161 224 (accept_3_2 19 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 161 224 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 161 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  17 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 224 (accept_3_2 16
  161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 161 224 7 2 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 161 224 (accept_3_2 13 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 224 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 224 (accept_3_2 10 161 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 224
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 8 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 161 224 7 1 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 161 224 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 161 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 161 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 224 (accept_3_2 4 161 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3
  161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 224 (accept_3_2 1 161 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 160 224 (Eq.refl Bool.true)
  (allA_of_3_0 65 160 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 159 224 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 159 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 224 (accept_3_2 64 159 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 159 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 224
  (Polychromatic418967fa.accept_20_2_19_4_1_3246 62 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 224 (accept_3_2 61 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 224 (Polychromatic418967fa.accept_17_9_6_3_1_2398 60 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 224 (accept_3_2 58 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 224 (accept_3_2 55 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 159 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 224 (accept_3_2 52 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 51 159 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 224 (accept_3_2 49 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 224 (accept_3_2 46 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 224
  (Polychromatic418967fa.accept_21_2_12_14_1_13354 44 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 159 224 (accept_3_2 43 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 159 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 159 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 159 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 224 (accept_3_2 40 159 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308
  39 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 224 (accept_3_2 37 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 224 (accept_3_2 34 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 224 (accept_3_2 31 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 224 (accept_3_2 28 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 159 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 224
  (Polychromatic418967fa.accept_17_9_6_3_1_2398 26 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 224 (accept_3_2 25 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 224 (Polychromatic418967fa.accept_21_3_12_14_1_8848 24 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 224 (accept_3_2 22 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 224 (accept_3_2 19 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 224 (accept_3_2 16 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 224 (accept_3_2 13 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 224 (accept_3_2 10 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 224 (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 224 (accept_3_2 7 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 224 (accept_3_2 4 159 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 159 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 224 (accept_3_2 1 159 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 158 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 158 224 2 33 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 224 2 32 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 224
  (Polychromatic418967fa.accept_13_11_2_3_1_883 63 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 224 2 31 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 224 (accept_3_2 61 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 224 2 30 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 224 2 29 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 224 2 28 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 224 (accept_3_2 55 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 224 2 27 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 224 2 26 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 224 2 25 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 224 (accept_3_2 49 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 224 2 24 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 224 2 23 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 224
  (Polychromatic418967fa.accept_21_3_11_14_1_13372 45 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 158 224 2 22 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 158 224 (accept_3_2 43 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 224 2 21 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 224 2 20 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 224 2 19 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 224 (accept_3_2 37 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 224 2 18 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 158 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 224 2 17 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 224 2 16 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 224 (accept_3_2 31 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 224 2 15 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 224 2 14 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 224
  (Polychromatic418967fa.accept_13_1_2_3_1_911 27 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 224 2 13 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 224 (accept_3_2 25 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 224 2 12 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 158 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 224 2 11 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 224 2 10 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 224 (accept_3_2 19 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 224 2 9 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 224 2 8 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 224 2 7 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 224 (accept_3_2 13 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 224 2 6 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 224 2 5 79 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 224 2 4 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 224 (accept_3_2 7 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  224 2 3 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 158 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 224 2 2 79 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 158 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 224 2 1 79 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 224 (accept_3_2 1 158 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 157 224 (Eq.refl Bool.true)
  (allA_of_3_0 68 157 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 156 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 156 224 4 17 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 224 (accept_3_2 67 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 224 2 33 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 224 4 16 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 224
  (Polychromatic418967fa.accept_19_6_4_15_1_2432 63 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 156 224 2 31 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 156 224 (accept_3_2 61 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 224 4 15 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 224 2 29 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 224
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 57 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 224 4 14 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 224 (accept_3_2 55 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 224 2 27 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 224 4 13 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 224 2 25 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 224 (accept_3_2 49 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 224 4 12 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 224 2 23 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 224 4 11 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 224 (accept_3_2 43 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 224 2 21 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 224 4 10 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 224
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 224 2 19 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 224 (accept_3_2 37 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 224 4 9 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 156 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 224 2 17 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33
  156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 224 4 8 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 224 (accept_3_2 31
  156 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 224 2 15 78 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 224 4 7 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 156 224 (Polychromatic418967fa.accept_19_8_4_15_1_1414 27 156 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 224 2 13 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 224 (accept_3_2 25 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 224 4 6 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 224 2 11 78 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 224
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 21 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 224 4 5 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 224 (accept_3_2 19 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  156 224 2 9 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 156 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 224 4 4 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15
  156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 224 2 7 78 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 224 (accept_3_2 13
  156 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 224 4 3 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 224 2 5 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 156 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 224 4 2 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 224 (accept_3_2 7 156 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 224 2 3 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 224 4 1 39 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 224
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 3 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 224 2 1 78 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 224 (accept_3_2 1 156 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 155 224 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 155 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 155 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 224 (accept_3_2 67 155 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 224 (Polychromatic418967fa.accept_9_3_2_8_1_108
  66 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 224
  (Polychromatic418967fa.accept_17_14_2_3_1_7172 65 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 224 (accept_3_2 64 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 224 (accept_3_2 61 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 155 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 224 (accept_3_2 58 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 224 (accept_3_2 55 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 224 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 155
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 224 (accept_3_2 52 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 224 (accept_3_2 49 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 224
  (Polychromatic418967fa.accept_15_2_5_14_1_61 47 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 224 (accept_3_2 46 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 224 (Polychromatic418967fa.accept_21_2_8_14_1_4148 44 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 224 (accept_3_2 43 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 155 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 224 (accept_3_2 40 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 224 (accept_3_2 37 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 155
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 224
  (Polychromatic418967fa.accept_13_9_12_3_1_907 35 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 224 (accept_3_2 34 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 224 (accept_3_2 31 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 224 (accept_3_2 28 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 224 (accept_3_2 25 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 155 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 224 (accept_3_2 22 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 224 (Polychromatic418967fa.accept_30_20_5_14_1_13371 20 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 224 (accept_3_2 19 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 224 (Polychromatic418967fa.accept_17_1_2_3_1_4668 18 155
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 224
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 224 (accept_3_2 16 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 224 (accept_3_2 13 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 224 (accept_3_2 10 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 8 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 224 (accept_3_2 7 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 155 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 224 (accept_3_2 4 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 224 (accept_3_2 1 155 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 154 224 (Eq.refl Bool.true) (allA_of_3_0 71 154 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 153 224 (Eq.refl Bool.true) (allA_succ_of_accept 71 153 224 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 224 (accept_3_2 70
  153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 69 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 224 (Polychromatic418967fa.accept_19_11_1_15_1_9263 68 153 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 224 (accept_3_2 67 153 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 153 224 (accept_3_2 64 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 153 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 153 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 62 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 224 (accept_3_2 61 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 153 224 (accept_3_2 58 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 153 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 153 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 56 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 224 (accept_3_2 55 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 153 224 (accept_3_2 52 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 153 224 (Polychromatic418967fa.accept_20_11_13_4_1_7573 51 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 153 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 50 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 224 (accept_3_2 49 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 224 (Polychromatic418967fa.accept_23_2_15_17_1_13370 48
  153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 224 (accept_3_2 46 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 153 224 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 153 224 (Polychromatic418967fa.accept_21_2_6_14_1_1569 44 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 224 (accept_3_2 43 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 224 (accept_3_2 40 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 38 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 224 (accept_3_2 37 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 224 (Polychromatic418967fa.accept_19_17_1_15_1_7901 36 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 224 (accept_3_2 34 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 224 (Polychromatic418967fa.accept_13_7_10_3_1_1505 33 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 224 (Polychromatic418967fa.accept_13_6_10_3_1_897 32 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 224 (accept_3_2 31 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 224 (accept_3_2 28 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 224 (accept_3_2 25 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 224 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 224 (accept_3_2 22 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 21 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 224 (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 224 (accept_3_2 19 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 224 (accept_3_2 16 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 224 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 224 (Polychromatic418967fa.accept_19_14_1_15_1_7914 14 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 224 (accept_3_2 13 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 224 (Polychromatic418967fa.accept_21_12_6_14_1_4146 12 153
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 224 (accept_3_2 10 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 224 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 224 (Polychromatic418967fa.accept_19_8_1_15_1_2496 8 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 224 (accept_3_2 7 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 224 (accept_3_2 4 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 153 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 224 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 224 (accept_3_2 1 153 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 152 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 152 224 8 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 152 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 71 152 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 224 2 35 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 224
  (Polychromatic418967fa.accept_25_19_2_24_1_11650 69 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 152 224 4 17 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 152 224 (accept_3_2 67 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 224 2 33 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 224 (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 152 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 224 8 8 19 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 224
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 224 2 31 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 224 (accept_3_2 61 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 224 4 15 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 224 (Polychromatic418967fa.accept_13_7_9_3_1_1504 59 152 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 224 2 29 76 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 224 8 7 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 152 224 (accept_3_2 55 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  152 224 2 27 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 152 224 (Polychromatic418967fa.accept_21_11_5_14_1_4142 53 152 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 224 4 13 38 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 224
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 51 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 224 2 25 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 224 (accept_3_2 49 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 224 8 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 152 224 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 152 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 224 2 23 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 224 (Polychromatic418967fa.accept_13_6_9_3_1_915
  45 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 152 224 4 11 38 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 152 224
  (accept_3_2 43 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 152 224 2 21 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 152 224
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 152 224 8 5 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 152 224 (Polychromatic418967fa.accept_21_18_5_14_1_11857 39 152 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 152 224 2 19 76 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 152 224 (accept_3_2 37 152 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 152 224 4 9 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 152 224 (Polychromatic418967fa.accept_11_2_9_4_1_310
  35 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 224 2 17 76 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 224
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 33 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 224 8 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 152 224 (accept_3_2 31 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  152 224 2 15 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 152 224 (Polychromatic418967fa.accept_21_8_5_14_1_5660 29 152 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 224 4 7 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 224 (Polychromatic418967fa.accept_10_7_2_4_1_569
  27 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 224 2 13 76 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 224
  (accept_3_2 25 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 224 8 3 19 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 224
  (Polychromatic418967fa.accept_27_23_17_8_1_13369 23 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 152 224 2 11 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 152 224 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 152 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 224 4 5 38 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 224 (accept_3_2 19 152 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 224 2 9 76 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 152 224 8 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 152 224 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 152 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 224 2 7 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 224 (accept_3_2 13 152 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 224 4 3 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 224 (Polychromatic418967fa.accept_21_11_5_14_1_4142 11 152
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 224 2 5 76 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 224
  (Polychromatic418967fa.accept_21_9_5_14_1_1568 9 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 224 8 1 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 224 (accept_3_2 7 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  224 2 3 76 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 152 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 224 4 1 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 224 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 152 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 224 2 1 76 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 224 (accept_3_2 1 152 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 152
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 151 224 (Eq.refl
  Bool.true) (allA_of_3_0 74 151 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 150 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 150 224 2 37 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 224 (accept_3_2 73 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 224 2 36 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 224 (Polychromatic418967fa.accept_19_14_17_15_1_3761 71 150 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 224 2 35 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 224
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 69 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 224 2 34 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 224 (accept_3_2 67 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 224 2 33 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 224 2 32 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 224
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 224 2 31 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 224 (accept_3_2 61 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 224 2 30 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 224 2 29 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 224 2 28 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 224 (accept_3_2 55 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 224 2 27 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 224 (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 150 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 224 2 26 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 224 2 25 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 224 (accept_3_2 49 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 224 2 24 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 224 2 23 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 224 2 22 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 224 (accept_3_2 43 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 224 2 21 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 224 2 20 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 224 2 19 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 224 (accept_3_2 37 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 224 2 18 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 224 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 150 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 224 2 17 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 224 2 16 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 224 (accept_3_2 31 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 224 2 15 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 224 2 14 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 224 2 13 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 224 (accept_3_2 25 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 224 2 12 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 224 2 11 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 224 2 10 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 224 (accept_3_2 19 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 224 2 9 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 224 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 224 2 8 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 224 2 7 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 224 (accept_3_2 13 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 224 2 6 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 224 2 5 75 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 224 2 4 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 224 (accept_3_2 7 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  224 2 3 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 150 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 224 2 2 75 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 224 2 1 75 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 224 (accept_3_2 1 150 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 149 224 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 224 (accept_3_2 73
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 224
  (Polychromatic418967fa.accept_17_4_13_3_1_7166 72 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 149 224 (Polychromatic418967fa.accept_18_17_5_8_1_1898 71 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 224 (accept_3_2 70 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 224 (Polychromatic418967fa.accept_10_8_9_4_1_961
  68 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 224 (accept_3_2 67
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 149 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 224 (accept_3_2 64 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 224 (Polychromatic418967fa.accept_12_2_5_8_1_159
  62 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 224 (accept_3_2 61
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 149 224 (Polychromatic418967fa.accept_17_8_13_3_1_3432 59 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 224 (accept_3_2 58 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 224 (accept_3_2 55
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 224
  (Polychromatic418967fa.accept_20_14_9_4_1_7517 54 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 149 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 53 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 224 (accept_3_2 52 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 224 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 224 (accept_3_2 49
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 149 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 224 (accept_3_2 46 149 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 224 (Polychromatic418967fa.accept_13_5_6_3_1_868
  44 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 224 (accept_3_2 43
  149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 149 224 (Polychromatic418967fa.accept_19_3_16_15_1_9281 41 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 224 (accept_3_2 40 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 224 (accept_3_2 37 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 224 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 224 (accept_3_2 34 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 224
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 32 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 224 (accept_3_2 31 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 224 (accept_3_2 28 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 224 (accept_3_2 25 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 224 (accept_3_2 22 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 224 (accept_3_2 19 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 224 (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 224 (accept_3_2 16 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 224 (accept_3_2 13 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 224 (accept_3_2 10 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 224 (accept_3_2 7 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 224 (accept_3_2 4 149 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 224 (accept_3_2 1 149 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 148 224 (Eq.refl
  Bool.true) (allA_of_3_0 77 148 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 147 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 77 147 224 7 11 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 147 224 (accept_3_2 76 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 147 224 (Polychromatic418967fa.accept_19_18_14_15_1_9277 75 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 224 (Polychromatic418967fa.accept_9_2_3_8_1_318
  74 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 224 (accept_3_2 73
  147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 72 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 147 224 7 10 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69
  147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 147 224 (accept_3_2 67 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 147 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 224 (accept_3_2 64 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 63 147 224 7 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 147 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 224 (accept_3_2 61 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595
  60 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 224 (accept_3_2 58 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 224 (Polychromatic418967fa.accept_20_17_7_4_1_7671 57 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 147 224 7 8 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 147 224 (accept_3_2 55 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 147 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 224 (accept_3_2 52 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595
  51 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 49 147 224 7 7 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 147 224 (Polychromatic418967fa.accept_17_14_11_3_1_4653 48 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 224 (accept_3_2 46
  147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 224
  (Polychromatic418967fa.accept_18_9_3_8_1_5419 45 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 224 (Polychromatic418967fa.accept_17_10_11_3_1_3442 44 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 224 (accept_3_2 43 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 224 7 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 224 (accept_3_2 40 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 224
  (Polychromatic418967fa.accept_15_9_12_14_1_963 39 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 224 (accept_3_2 37 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 224 (Polychromatic418967fa.accept_17_2_11_3_1_4654 36 147 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 147 224 7 5 21 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 147 224 (accept_3_2 34 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595
  33 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 224 (accept_3_2 31 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 147 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 147 224 7 4 21 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 147 224
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 224 (accept_3_2 25 147 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 224
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 224 (accept_3_2 22 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  147 224 7 3 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 147 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 147 224 (accept_3_2 19 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 147 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 224 (accept_3_2 16 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595
  15 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 147 224 7 2 21 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 224
  (accept_3_2 13 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 224 (accept_3_2 10 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 224 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 147 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 224
  (Polychromatic418967fa.accept_22_8_15_4_1_13368 8 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 147 224 7 1 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 147 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 224 (accept_3_2 4 147 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 3
  147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 224 (accept_3_2 1 147 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 146 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 146 224 2 39 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 146 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 146 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 224 2 38 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 224 2 37 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 224 (accept_3_2 73 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 224 2 36 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 146 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 224 2 35 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 69 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 224 2 34 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 224 (accept_3_2 67 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 224 2 33 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 224 2 32 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 224
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 146 224 2 31 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 146 224 (accept_3_2 61 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 224 2 30 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 224 2 29 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 224 2 28 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 224 (accept_3_2 55 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 224 2 27 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 224 2 26 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 224 2 25 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 224 (accept_3_2 49 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 224 2 24 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 146 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 224 2 23 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 224 2 22 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 224 (accept_3_2 43 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 224 2 21 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 224 2 20 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 224 2 19 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 224 (accept_3_2 37 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 224 2 18 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 224 2 17 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 224 2 16 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 224 (accept_3_2 31 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 224 2 15 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 29 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 224 2 14 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 224
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 146 224 2 13 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 146 224 (accept_3_2 25 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 224 2 12 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 224 2 11 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 224 2 10 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 224 (accept_3_2 19 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 224 2 9 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 146 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 224 2 8 73 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 224 2 7 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 224 (accept_3_2 13 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 224 2 6 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 146 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 224 2 5 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 224
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 224 2 4 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 224 (accept_3_2 7 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  224 2 3 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 224 2 2 73 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 146 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 224 2 1 73 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 224 (accept_3_2 1 146 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 145 224 (Eq.refl
  Bool.true) (allA_of_3_0 80 145 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 144 224 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 144 224 16 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 144 224 (accept_3_2 79 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  144 224 2 39 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 144 224 (Polychromatic418967fa.accept_19_1_11_15_1_2459 77 144 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 224 4 19 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 224
  (Polychromatic418967fa.accept_21_12_18_14_1_8854 75 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 144 224 2 37 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 144 224 (accept_3_2 73 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 224 8 9 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522 71 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 224 2 35 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 224 (Polychromatic418967fa.accept_13_4_1_3_1_3058
  69 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 224 4 17 36 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 224
  (accept_3_2 67 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 224 2 33 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 224
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 65 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 224 16 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 144 224 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 224 2 31 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 224 (accept_3_2 61 144 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 224 4 15 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 224 (Polychromatic418967fa.accept_13_7_1_3_1_1523 59 144
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 224 2 29 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 224
  (Polychromatic418967fa.accept_13_5_1_3_1_878 57 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 224 8 7 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 144 224 (accept_3_2 55 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  144 224 2 27 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 144 224 (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 224 4 13 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457
  51 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 224 2 25 72 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 224
  (accept_3_2 49 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 224 16 3 9 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 224
  (Polychromatic418967fa.accept_17_13_8_3_1_7177 47 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 224 2 23 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 224 (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 144 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 224 4 11 36 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 224 (accept_3_2 43 144 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 224 2 21 72 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 224
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 224 8 5 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 144 224 (Polychromatic418967fa.accept_17_5_8_3_1_1419 39 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 224 2 19 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 224 (accept_3_2 37 144 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 224 4 9 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 224 (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 144
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 224 2 17 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 224
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 224 16 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 144 224 (accept_3_2 31 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  144 224 2 15 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 224 (Polychromatic418967fa.accept_17_12_8_3_1_4646 29 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 224 4 7 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 224
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 144 224 2 13 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 144 224 (accept_3_2 25 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 224 8 3 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 224 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 224 2 11 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457
  21 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 224 4 5 36 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 224
  (accept_3_2 19 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 224 2 9 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 224
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 224 16 1 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 224 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 144 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 224 2 7 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 224 (accept_3_2 13 144 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 224 4 3 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 224 (Polychromatic418967fa.accept_13_11_1_3_1_910 11 144
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 224 2 5 72 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 224
  (Polychromatic418967fa.accept_19_9_11_15_1_6406 9 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 224 8 1 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 224 (accept_3_2 7 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  224 2 3 72 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 224 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 144 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 224 4 1 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 224 (Polychromatic418967fa.accept_27_3_9_8_1_13367 3 144 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 224 2 1 72 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 224 (accept_3_2 1 144 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 143 224 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 143 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 224 (Polychromatic418967fa.accept_15_5_8_14_1_432
  80 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 224 (accept_3_2 79
  143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 224
  (Polychromatic418967fa.accept_17_10_7_3_1_727 78 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 143 224 (Polychromatic418967fa.accept_10_7_3_4_1_978 77 143 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 224 (accept_3_2 76 143 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504
  74 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 224 (accept_3_2 73
  143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 224
  (Polychromatic418967fa.accept_17_4_7_3_1_1417 72 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 143 224 (Polychromatic418967fa.accept_19_14_10_15_1_13366 71 143 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 224 (accept_3_2 70 143 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 224
  (Polychromatic418967fa.accept_19_11_10_15_1_3741 68 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 143 224 (accept_3_2 67 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 143 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575 66 143 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 224 (accept_3_2 64 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 143 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 224 (accept_3_2 61 143 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 143 224 (Polychromatic418967fa.accept_19_3_10_15_1_9241 60 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 59 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 224 (accept_3_2 58 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 224 (Polychromatic418967fa.accept_18_2_17_8_1_1893 56 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 224 (accept_3_2 55 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 224 (Polychromatic418967fa.accept_15_9_8_14_1_1699 54 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 224
  (Polychromatic418967fa.accept_20_13_3_4_1_6036 53 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 224 (accept_3_2 52 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 224 (accept_3_2 49 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 224 (Polychromatic418967fa.accept_25_23_18_24_1_13365 48
  143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 47 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 224 (accept_3_2 46 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 224 (Polychromatic418967fa.accept_17_10_7_3_1_727 44 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 224 (accept_3_2 43 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 224 (Polychromatic418967fa.accept_19_4_10_15_1_9243 42 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 224 (accept_3_2 40 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 224 (accept_3_2 37 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 224
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 224 (accept_3_2 34 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 224 (Polychromatic418967fa.accept_22_10_11_4_1_6974 32 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 224 (accept_3_2 31 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 224 (Polychromatic418967fa.accept_19_11_10_15_1_3741 30
  143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 224
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 224 (accept_3_2 28 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 224 (accept_3_2 25 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 224 (Polychromatic418967fa.accept_15_9_8_14_1_1699 24 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 224
  (Polychromatic418967fa.accept_18_5_17_8_1_2984 23 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 224 (accept_3_2 22 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 20 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 224 (accept_3_2 19 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 224 (Polychromatic418967fa.accept_21_18_17_14_1_10491 18
  143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 224
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 224 (accept_3_2 16 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 224 (accept_3_2 13 143 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 224 (Polychromatic418967fa.accept_17_12_7_3_1_1498 12 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 224
  (Polychromatic418967fa.accept_19_11_10_15_1_3741 11 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 143 224 (accept_3_2 10 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 224 (Polychromatic418967fa.accept_21_8_17_14_1_4156 8 143
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 224 (accept_3_2 7 143 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 224 (Polychromatic418967fa.accept_15_6_8_14_1_4575
  6 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 224
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 224 (accept_3_2 4 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 224 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 143 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 224 (accept_3_2 1 143 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 142 224 (Eq.refl
  Bool.true) (allA_of_3_0 83 142 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 141 224 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 141 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 224 (accept_3_2 82 141 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 224 (Polychromatic418967fa.accept_21_18_15_14_1_8871 81 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 224
  (Polychromatic418967fa.accept_13_2_11_3_1_873 80 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 141 224 (accept_3_2 79 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 141 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 224 (accept_3_2 76 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 224 (accept_3_2 73 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 141 224 (Polychromatic418967fa.accept_13_7_11_3_1_1540 72 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 224 (accept_3_2 70 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 141 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 141 224 (accept_3_2 67 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 224 (accept_3_2 64 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 224 (Polychromatic418967fa.accept_20_3_1_4_1_7654 63 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 224
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 62 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 141 224 (accept_3_2 61 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 141 224 (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 141 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 141 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 224 (accept_3_2 58 141 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308
  57 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 224 (accept_3_2 55 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 141 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 224 (accept_3_2 52 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 224 (Polychromatic418967fa.accept_20_11_1_4_1_7543 51 141 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 224 (accept_3_2 49 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 224 (accept_3_2 46 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 224
  (Polychromatic418967fa.accept_13_5_11_3_1_902 44 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 224 (accept_3_2 43 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 141 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 224 (accept_3_2 40 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 224 (accept_3_2 37 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 224 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 224 (accept_3_2 34 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 224 (Polychromatic418967fa.accept_13_7_11_3_1_1540 33 141 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 224 (accept_3_2 31 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 224 (accept_3_2 28 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 224
  (Polychromatic418967fa.accept_19_7_8_15_1_2448 26 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 224 (accept_3_2 25 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 224 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 224 (accept_3_2 22 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 224 (accept_3_2 19 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 224 (accept_3_2 16 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 224
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 224 (accept_3_2 13 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 224 (accept_3_2 10 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 224 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 224
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 8 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 224 (accept_3_2 7 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 224 (accept_3_2 4 141 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 141 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 224
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 224 (accept_3_2 1 141 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 140 224
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 140 224 28 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 140 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 140 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 224 2 41 70 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 224
  (Polychromatic418967fa.accept_15_6_5_14_1_429 81 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 224 4 20 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 224 (accept_3_2 79 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 224 2 39 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 140 224 7 11 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 140 224 4 19 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 140 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 140 224 2 37 70 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 140 224 (accept_3_2 73
  140 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 140 224 4 18 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 140 224
  (Polychromatic418967fa.accept_13_6_10_3_1_897 71 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 140 224 14 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 140 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 140 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 140 224 4 17 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 140 224 (accept_3_2 67 140 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 140 224 2 33 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 140 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65
  140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 224 4 16 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 140 224 7 9 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 140 224 2 31 70 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 140 224
  (accept_3_2 61 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 140 224 4 15 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 140 224
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 59 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 140 224 2 29 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 140 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 140 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 140 224 28 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 140 224 (accept_3_2 55 140 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 140 224 2 27 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 140 224 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 140
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 224 4 13 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 224 2 25 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 140 224 7 7 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 140 224 4 12 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 140 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 224 2 23 70 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 224
  (Polychromatic418967fa.accept_11_1_8_4_1_717 45 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 224 4 11 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 224 (accept_3_2 43 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 224 14 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 224 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 140 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 224 4 10 35 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 224
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 224 2 19 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 224 (accept_3_2 37 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 224 4 9 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 140 224 7 5 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 140 224 2 17 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 140 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 140 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 224 4 8 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 224 (accept_3_2 31 140 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 224 2 15 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29
  140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 224 28 1 5 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 224
  (Polychromatic418967fa.accept_19_8_7_15_1_13364 27 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 140 224 2 13 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 140 224 (accept_3_2 25 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 224 4 6 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 140 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 23 140 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 224 2 11 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 140 224 7 3 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 140 224 4 5 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 224 (accept_3_2 19 140 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 224 2 9 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 140 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 224 4 4 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 224
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 224 14 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 140 224 (accept_3_2 13 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 224 4 3 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 140 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 224 2 5 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 9
  140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 224 4 2 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 140 224 7 1 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 140 224 2 3 70 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 224
  (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 140 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 140 224 4 1 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 140 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 140 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 224 2 1 70 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 224 (accept_3_2 1 140 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 139 224
  (Eq.refl Bool.true) (allA_of_3_0 86 139 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 138 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 138 224 2 43 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 138 224 (accept_3_2 85 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 224 2 42 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 224 2 41 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 224 2 40 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 224 (accept_3_2 79 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 224 2 39 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 224 2 38 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 224 2 37 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 224 (accept_3_2 73 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 224 2 36 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 224 (Polychromatic418967fa.accept_15_11_3_14_1_971 71 138 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 224 2 35 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 224 2 34 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 224 (accept_3_2 67 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 224 2 33 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 224 2 32 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 224 2 31 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 224 (accept_3_2 61 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 224 2 30 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 224 2 29 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 224
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 224 2 28 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 224 (accept_3_2 55 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 224 2 27 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 224 (Polychromatic418967fa.accept_21_11_12_14_1_5670 53 138 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 224 2 26 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 224 2 25 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 224 (accept_3_2 49 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 224 2 24 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 224 2 23 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 224 2 22 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 224 (accept_3_2 43 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 224 2 21 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 224 2 20 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 224 2 19 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 224 (accept_3_2 37 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 224 2 18 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 224 (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 138 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 224 2 17 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 224 2 16 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 224 (accept_3_2 31 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 224 2 15 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 224 2 14 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 224 2 13 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 224 (accept_3_2 25 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 224 2 12 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 224 2 11 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 224 2 10 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 224 (accept_3_2 19 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 224 2 9 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 224 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 138 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 224 2 8 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 224
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 224 2 7 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 224 (accept_3_2 13 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 224 2 6 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 224 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 224 2 5 69 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 224
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 224 2 4 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 224 (accept_3_2 7 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  224 2 3 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 224 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 224 2 2 69 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 138 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 224 2 1 69 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 224 (accept_3_2 1 138 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 137 224
  (Eq.refl Bool.true) (allA_succ_of_accept 87 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 224 (accept_3_2 85 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 137 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 83 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 224 (accept_3_2 82 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 224
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 80 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 224 (accept_3_2 79 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 224 (accept_3_2 76 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 224 (accept_3_2 73 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 224 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 71 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 224 (accept_3_2 70 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 224 (accept_3_2 67 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 65 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 224 (accept_3_2 64 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 62 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 224 (accept_3_2 61 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 224 (accept_3_2 58 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 224
  (Polychromatic418967fa.accept_13_4_7_3_1_92 56 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 224 (accept_3_2 55 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 224 (Polychromatic418967fa.accept_11_10_5_4_1_711 54 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 224 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 224 (accept_3_2 52 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 224 (accept_3_2 49 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 224 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 224 (accept_3_2 46 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 224
  (Polychromatic418967fa.accept_19_6_4_15_1_2432 44 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 224 (accept_3_2 43 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 224 (accept_3_2 40 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 224 (accept_3_2 37 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 224 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 224 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 224 (accept_3_2 34 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 224 (accept_3_2 31 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 224 (Polychromatic418967fa.accept_19_10_4_15_1_3720 29 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 224 (accept_3_2 28 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 224 (accept_3_2 25 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 224 (accept_3_2 22 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 224
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 224 (accept_3_2 19 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 224 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 224 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 224 (accept_3_2 16 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 224 (accept_3_2 13 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 224 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 224 (accept_3_2 10 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 224
  (Polychromatic418967fa.accept_13_8_7_3_1_430 8 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 224 (accept_3_2 7 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 224 (accept_3_2 4 137 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 224
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 224 (accept_3_2 1 137 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 136 224
  (Eq.refl Bool.true) (allA_of_3_0 89 136 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 135 224 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 224 (accept_3_2 88 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 224 (Polychromatic418967fa.accept_13_9_5_3_1_428 87 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 86 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 135 224 (accept_3_2 85 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 135 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 84 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 224 (accept_3_2 82 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 224
  (Polychromatic418967fa.accept_13_2_5_3_1_406 80 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 135 224 (accept_3_2 79 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 135 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 224 (accept_3_2 76 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 224 (Polychromatic418967fa.accept_17_7_16_3_1_4660 75 135 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 224
  (Polychromatic418967fa.accept_13_9_5_3_1_428 74 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 224 (accept_3_2 73 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 135 224 (Polychromatic418967fa.accept_17_4_16_3_1_4620 72 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 224 (accept_3_2 70 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 69 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 224
  (Polychromatic418967fa.accept_19_11_2_15_1_5062 68 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 135 224 (accept_3_2 67 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 135 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 135 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 135 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 224 (accept_3_2 64 135 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 224 (Polychromatic418967fa.accept_13_11_5_3_1_889
  63 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 224
  (Polychromatic418967fa.accept_11_7_3_4_1_729 62 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 224 (accept_3_2 61 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 135 224 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 224 (accept_3_2 58 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 57 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 224 (accept_3_2 55 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 224 (accept_3_2 52 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 224
  (Polychromatic418967fa.accept_13_11_5_3_1_889 50 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 224 (accept_3_2 49 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 224 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 224 (accept_3_2 46 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 224 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 224
  (Polychromatic418967fa.accept_19_6_2_15_1_9266 44 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 224 (accept_3_2 43 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 224 (accept_3_2 40 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 224
  (Polychromatic418967fa.accept_17_4_16_3_1_4620 38 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 224 (accept_3_2 37 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 224 (accept_3_2 34 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 224 (Polychromatic418967fa.accept_25_8_10_24_1_13363 33 135 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 224
  (Polychromatic418967fa.accept_13_6_5_3_1_426 32 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 224 (accept_3_2 31 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 224 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 224 (accept_3_2 28 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 224 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 224 (accept_3_2 25 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 224 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 224 (accept_3_2 22 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 224 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 224
  (Polychromatic418967fa.accept_19_1_2_15_1_3684 20 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 224 (accept_3_2 19 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 224 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 224 (accept_3_2 16 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 224 (Polychromatic418967fa.accept_13_2_5_3_1_406 15 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 224
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 224 (accept_3_2 13 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 224 (Polychromatic418967fa.accept_23_12_20_17_1_13362 12 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 224 (accept_3_2 10 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 135 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 224
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 224 (accept_3_2 7 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 224 (accept_3_2 4 135 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 224 (Polychromatic418967fa.accept_18_3_9_8_1_2977 3 135 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 224
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 224 (accept_3_2 1 135 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 134 224
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 134 224 2 45 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 134 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 134 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 224 2 44 67 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 224
  (Polychromatic418967fa.accept_19_11_1_15_1_9263 87 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 134 224 2 43 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 134 224 (accept_3_2 85 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 224 2 42 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 83 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 224 2 41 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 224
  (Polychromatic418967fa.accept_19_5_1_15_1_9264 81 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 224 2 40 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 224 (accept_3_2 79 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 224 2 39 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 134 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 224 2 38 67 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 224
  (Polychromatic418967fa.accept_11_9_2_4_1_707 75 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 224 2 37 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 224 (accept_3_2 73 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 224 2 36 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 224 2 35 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 224
  (Polychromatic418967fa.accept_17_1_15_3_1_1501 69 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 224 2 34 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 224 (accept_3_2 67 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 224 2 33 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 134 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 224 2 32 67 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 224
  (Polychromatic418967fa.accept_17_12_15_3_1_7168 63 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 134 224 2 31 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 134 224 (accept_3_2 61 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 224 2 30 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 224 2 29 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 224
  (Polychromatic418967fa.accept_21_15_8_14_1_8860 57 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 134 224 2 28 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 134 224 (accept_3_2 55 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 224 2 27 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 224 (Polychromatic418967fa.accept_11_9_2_4_1_707 53 134 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 224 2 26 67 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 224
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 51 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 224 2 25 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 224 (accept_3_2 49 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 224 2 24 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 224 2 23 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 224
  (Polychromatic418967fa.accept_21_3_8_14_1_8864 45 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 224 2 22 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 224 (accept_3_2 43 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 224 2 21 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 134 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 224 2 20 67 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 224
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 224 2 19 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 224 (accept_3_2 37 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 224 2 18 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 224 2 17 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 224
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 224 2 16 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 224 (accept_3_2 31 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 224 2 15 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 134 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 224 2 14 67 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 224
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 224 2 13 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 224 (accept_3_2 25 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 224 2 12 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 224 2 11 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 224
  (Polychromatic418967fa.accept_19_2_1_15_1_2494 21 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 224 2 10 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 224 (accept_3_2 19 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 224 2 9 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 224 (Polychromatic418967fa.accept_11_6_2_4_1_1703 17 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 224 2 8 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 224
  (Polychromatic418967fa.accept_21_15_8_14_1_8860 15 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 134 224 2 7 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 134 224 (accept_3_2 13 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 224 2 6 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 224 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 224 2 5 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 224
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 224 2 4 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 224 (accept_3_2 7 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  224 2 3 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 224 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 134 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 224 2 2 67 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 224 (Polychromatic418967fa.accept_20_3_14_4_1_7632 3 134 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 224 2 1 67 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 224 (accept_3_2 1 134 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 133 224
  (Eq.refl Bool.true) (allA_of_3_0 92 133 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 132 224 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 132 224 4 23 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 132 224 (accept_3_2 91 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 224 2 45 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 224 (Polychromatic418967fa.accept_13_11_2_3_1_883 89 132 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 224 4 22 33 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 87 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 224 2 43 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 224 (accept_3_2 85 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 224 4 21 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 224 2 41 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 224
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 81 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 224 4 20 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 224 (accept_3_2 79 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 224 2 39 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 224 4 19 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 224 2 37 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 224 (accept_3_2 73 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 224 4 18 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 224 (Polychromatic418967fa.accept_15_11_12_14_1_2612 71 132 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 224 2 35 66 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 224
  (Polychromatic418967fa.accept_15_9_12_14_1_963 69 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 224 4 17 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 224 (accept_3_2 67 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 224 2 33 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 224 4 16 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 224
  (Polychromatic418967fa.accept_13_11_2_3_1_883 63 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 132 224 2 31 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 132 224 (accept_3_2 61 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 224 4 15 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 224 2 29 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 224 4 14 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 224 (accept_3_2 55 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 224 2 27 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 224 (Polychromatic418967fa.accept_13_1_2_3_1_911 53 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 224 4 13 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 224
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 51 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 224 2 25 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 224 (accept_3_2 49 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 224 4 12 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 224 2 23 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 224
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 45 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 224 4 11 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 224 (accept_3_2 43 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 224 2 21 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 224 4 10 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 224
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 224 2 19 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 224 (accept_3_2 37 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 224 4 9 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 224 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 132 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 224 2 17 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 224
  (Polychromatic418967fa.accept_17_16_13_3_1_4677 33 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 132 224 4 8 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 132 224 (accept_3_2 31 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 224 2 15 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 224 4 7 33 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 224 2 13 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 224 (accept_3_2 25 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 224 4 6 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 224 2 11 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 21
  132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 224 4 5 33 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 224 (accept_3_2 19
  132 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 224 2 9 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 224
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 224 4 4 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 132 224 (Polychromatic418967fa.accept_27_15_24_8_1_13361 15 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 224 2 7 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 224 (accept_3_2 13 132 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 224 4 3 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 224 (Polychromatic418967fa.accept_9_2_6_8_1_321 11
  132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 224 2 5 66 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 224
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 224 4 2 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 224 (accept_3_2 7 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  224 2 3 66 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 224 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 224 4 1 33 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 224 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 132 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 224 2 1 66 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 224 (accept_3_2 1 132 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 131
  224 (Eq.refl Bool.true) (allA_succ_of_accept 93 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 131 224 (accept_3_2 91 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 131 224 (Polychromatic418967fa.accept_19_14_17_15_1_3761 90 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 224 (Polychromatic418967fa.accept_13_11_1_3_1_910 89 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 224 (accept_3_2 88 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 224 (accept_3_2 85 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 224 (accept_3_2 82 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 224
  (Polychromatic418967fa.accept_13_2_1_3_1_419 80 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 224 (accept_3_2 79 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 77 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 224 (accept_3_2 76 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 224 (accept_3_2 73 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 224 (Polychromatic418967fa.accept_13_7_1_3_1_1523 72 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 224 (Polychromatic418967fa.accept_11_5_10_4_1_1157 71 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 224 (accept_3_2 70 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 224
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 68 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 224 (accept_3_2 67 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 224 (accept_3_2 64 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 224 (accept_3_2 61 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 224 (Polychromatic418967fa.accept_13_7_1_3_1_1523 59 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 224 (accept_3_2 58 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 224 (accept_3_2 55 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 224 (Polychromatic418967fa.accept_13_2_1_3_1_419 54 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 224 (Polychromatic418967fa.accept_18_17_5_8_1_1898 53 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 224 (accept_3_2 52 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 224 (accept_3_2 49 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 224 (accept_3_2 46 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 224
  (Polychromatic418967fa.accept_13_5_1_3_1_878 44 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 224 (accept_3_2 43 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 224 (Polychromatic418967fa.accept_13_2_1_3_1_419 41 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 224 (accept_3_2 40 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 224 (accept_3_2 37 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 224 (Polychromatic418967fa.accept_21_15_5_14_1_11856 36 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 224 (accept_3_2 34 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 224
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 32 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 224 (accept_3_2 31 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 224 (accept_3_2 28 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 224 (accept_3_2 25 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 224 (Polychromatic418967fa.accept_29_23_15_21_1_13360 23 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 224 (accept_3_2 22 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 224 (accept_3_2 19 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 224 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 224 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 224 (accept_3_2 16 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 224
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 224 (accept_3_2 13 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 224 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 224 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 224 (accept_3_2 10 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 224
  (Polychromatic418967fa.accept_17_8_12_3_1_5927 8 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 224 (accept_3_2 7 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 224 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 224 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 224 (accept_3_2 4 131 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 224
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 224 (accept_3_2 1 131 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 130
  224 (Eq.refl Bool.true) (allA_of_3_0 95 130 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 129 224
  (Eq.refl Bool.true) (allA_succ_of_accept 95 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 224 (accept_3_2 94 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 93 129
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 224 (accept_3_2 91 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 129 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 224 (accept_3_2 88 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 224 (accept_3_2 85 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 129 224 (Polychromatic418967fa.accept_11_7_8_4_1_718 84 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 224 (accept_3_2 82 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 81 129 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 224
  (Polychromatic418967fa.accept_13_2_12_3_1_415 80 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 224 (accept_3_2 79 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 224 (accept_3_2 76 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 75 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 224 (accept_3_2 73 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 224 (accept_3_2 70 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 224 (accept_3_2 67 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 224 (accept_3_2 64 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 224
  (Polychromatic418967fa.accept_11_7_8_4_1_718 62 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 224 (accept_3_2 61 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 224 (accept_3_2 58 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 129 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 224 (accept_3_2 55 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 224 (accept_3_2 52 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 224 (accept_3_2 49 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 224 (accept_3_2 46 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 224 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 224
  (Polychromatic418967fa.accept_21_2_3_14_1_5690 44 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 224 (accept_3_2 43 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 224 (accept_3_2 40 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 224 (Polychromatic418967fa.accept_20_19_9_4_1_7560 39 129 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 224 (accept_3_2 37 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 224 (accept_3_2 34 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 224 (accept_3_2 31 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 224 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 224 (accept_3_2 28 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 224 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 129 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 224
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 26 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 224 (accept_3_2 25 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 224 (accept_3_2 22 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 224 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 129 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 224 (accept_3_2 19 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 224 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 224 (accept_3_2 16 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 224
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 224 (accept_3_2 13 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 224 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 224 (accept_3_2 10 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 224 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 224
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 224 (accept_3_2 7 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 224 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 224 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 224 (accept_3_2 4 129 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 224 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 129 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 224
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 224 (accept_3_2 1 129 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  224)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 128
  224 (Eq.refl Bool.true) (allA_succ_of_gcd 96 128 224 32 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 128 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 95 128 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 224 2 47 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 93 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 128 224 4 23 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 128 224 (accept_3_2 91 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 128 224 2 45 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 128 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 89 128 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 224 8 11 16 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 87 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 224 2 43 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 224 (accept_3_2 85 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 224 4 21 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 224 (Polychromatic418967fa.accept_13_5_11_3_1_902 83 128 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 224 2 41 64 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 224
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 224 16 5 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 128 224 (accept_3_2 79 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  128 224 2 39 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 128 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 128 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 224 4 19 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 75
  128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 128 224 2 37 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 128 224 (accept_3_2 73
  128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 128 224 8 9 16 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 128 224
  (Polychromatic418967fa.accept_18_17_2_8_1_6800 71 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 128 224 2 35 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 128 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 69 128 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 128 224 4 17 32 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 128 224 (accept_3_2 67 128 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 128 224 2 33 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 128 224 (Polychromatic418967fa.accept_15_5_8_14_1_432
  65 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 224 32 2 4 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 224
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 224 2 31 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 224 (accept_3_2 61 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 224 4 15 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 224 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 128 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 224 2 29 64 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 224
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 224 8 7 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 128 224 (accept_3_2 55 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  128 224 2 27 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 128 224 (Polychromatic418967fa.accept_13_1_11_3_1_901 53 128 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 224 4 13 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 224 (Polychromatic418967fa.accept_9_6_2_8_1_592 51
  128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 128 224 2 25 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 128 224 (accept_3_2 49
  128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 128 224 16 3 8 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 128 224
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 47 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 128 224 2 23 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 128 224 (Polychromatic418967fa.accept_17_11_9_3_1_1463 45 128 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 128 224 4 11 32 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 128 224 (accept_3_2 43 128 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 128 224 2 21 64 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 128 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 128 224 8 5 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 128 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 128 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 128 224 2 19 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 128 224 (accept_3_2 37 128 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 128 224 4 9 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 224 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 128
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 224 2 17 64 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 224 32 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 128 224 (accept_3_2 31 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  128 224 2 15 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 128 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 128 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 224 4 7 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 224 (Polychromatic418967fa.accept_13_1_11_3_1_901
  27 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 224 2 13 64 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 224
  (accept_3_2 25 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 224 8 3 16 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 128 224 2 11 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 128 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 128 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 224 4 5 32 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 224 (accept_3_2 19 128 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 224 2 9 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 224 (Polychromatic418967fa.accept_18_17_2_8_1_6800
  17 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 224 16 1 8 14
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 224
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 224 2 7 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 128 224 (accept_3_2 13 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 224 4 3 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 128 224 (Polychromatic418967fa.accept_17_11_9_3_1_1463 11 128 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 224 2 5 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 224 (Polychromatic418967fa.accept_10_9_8_4_1_970 9
  128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 224 8 1 16 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 224 (accept_3_2 7
  128 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 224 2 3 64 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 224
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 128 224 4 1 32 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 128 224 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 128 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 224 2 1 64 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 224 (accept_3_2 1 128 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  127 224 (Eq.refl Bool.true) (allA_of_3_0 98 127 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 126 224
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 126 224 14 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 126 224 (accept_3_2 97 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 224 2 48 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 95 126 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 224 2 47 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 224 2 46 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 91 126 224 7 13 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 126 224 2 45 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 126 224 (Polychromatic418967fa.accept_17_4_7_3_1_1417 89 126
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 224 2 44 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 224
  (Polychromatic418967fa.accept_11_10_5_4_1_711 87 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 224 2 43 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 224 (accept_3_2 85 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 224 14 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 126 224 (Polychromatic418967fa.accept_13_5_9_3_1_870 83 126 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 224 2 41 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 224 (Polychromatic418967fa.accept_12_9_6_8_1_518
  81 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 224 2 40 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 224
  (accept_3_2 79 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 126 224 2 39 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 126 224 7 11 18 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 126 224 2 38 63
  112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 75 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 224 2 37 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 224 (accept_3_2 73 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 224 2 36 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 224 (Polychromatic418967fa.accept_13_6_9_3_1_915 71 126 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 224 14 5 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 224 2 34 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 224 (accept_3_2 67 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 224 2 33 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 126 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 224 2 32 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 224 7 9 18 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 224 2 31 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 224 (accept_3_2 61 126 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 224 2 30 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 224
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 59 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 224 2 29 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 57 126 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 224 14 4 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 224 (accept_3_2 55 126 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 126 224 2 27 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 126 224 (Polychromatic418967fa.accept_15_8_6_14_1_975
  53 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 224 2 26 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 224 2 25 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 126 224 7 7 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 126 224 2 24 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 224 (Polychromatic418967fa.accept_13_8_9_3_1_2213 47 126 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 224 2 23 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 224 2 22 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 224 (accept_3_2 43 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 224 14 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 224 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 126 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 224 2 20 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 224 (Polychromatic418967fa.accept_12_3_6_8_1_969
  39 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 224 2 19 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 224
  (accept_3_2 37 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 224 2 18 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 224 7 5 18 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 224 2 17 63 112
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 224
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 224 2 16 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 224 (accept_3_2 31 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 224 2 15 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 224 (Polychromatic418967fa.accept_17_12_7_3_1_1498 29 126 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 224 14 2 9 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 224
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 224 2 13 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 224 (accept_3_2 25 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 224 2 12 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 224 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 126 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 224 2 11 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 224 7 3 18 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 224 2 10 63 112 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 224 (accept_3_2 19
  126 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 224 2 9 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 224
  (Polychromatic418967fa.accept_19_17_12_15_1_11981 17 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 126 224 2 8 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 126 224 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 126 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 224 14 1 9 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 224 (accept_3_2 13 126 224
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 224 2 6 63 112 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 224
  (Polychromatic418967fa.accept_22_11_16_4_1_10352 11 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 126 224 2 5 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 126 224 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 224 2 4 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 224 7 1 18 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 224 2 3 63 112 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 224
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 126 224 2 2 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 126 224 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 126 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 224 2 1 63 112 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 224 (accept_3_2 1 126 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 126
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  125 224 (Eq.refl Bool.true) (allA_succ_of_accept 99 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 125 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 224
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 125 224 (accept_3_2 97 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 125 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 125 224 (Polychromatic418967fa.accept_18_5_17_8_1_2984 95 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 125 224 (accept_3_2 94 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 224
  (Polychromatic418967fa.accept_15_2_5_14_1_61 92 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 125 224 (accept_3_2 91 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 125 224 (Polychromatic418967fa.accept_17_5_6_3_1_4640 90 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 125 224 (Polychromatic418967fa.accept_10_9_5_4_1_966 89 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 224 (accept_3_2 88 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 125 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 224
  (Polychromatic418967fa.accept_10_6_5_4_1_571 86 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 125 224 (accept_3_2 85 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 125 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 84 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 125 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 83 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 224 (accept_3_2 82 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 224
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 224
  (Polychromatic418967fa.accept_19_4_11_15_1_3743 80 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 125 224 (accept_3_2 79 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 125 224 (Polychromatic418967fa.accept_19_2_11_15_1_2404 78 125 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 224 (Polychromatic418967fa.accept_15_2_5_14_1_61
  77 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 224 (accept_3_2 76
  125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 224
  (Polychromatic418967fa.accept_6_3_5_2_1_12 75 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 125 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 125 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 224 (accept_3_2 73 125 224 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 125 224 (Polychromatic418967fa.accept_13_7_8_3_1_1533 72 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 71 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 224 (accept_3_2 70 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 224 (Polychromatic418967fa.accept_15_8_5_14_1_986 68 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 224 (accept_3_2 67 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 224
  (Polychromatic418967fa.accept_17_14_6_3_1_2362 65 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 224 (accept_3_2 64 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 224 (accept_3_2 61 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 224 (Polychromatic418967fa.accept_17_9_6_3_1_2398 60 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 59 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 224 (accept_3_2 58 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 224 (accept_3_2 55 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 224 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 224 (accept_3_2 52 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 224 (accept_3_2 49 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 224 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 224
  (Polychromatic418967fa.accept_15_2_5_14_1_61 47 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 224 (accept_3_2 46 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 224 (accept_3_2 43 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 224 (Polychromatic418967fa.accept_19_4_11_15_1_3743 42 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 41 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 224 (accept_3_2 40 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 224 (accept_3_2 37 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 224
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 224 (accept_3_2 34 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 224 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 224 (accept_3_2 31 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 224 (Polychromatic418967fa.accept_20_10_5_4_1_7511 30 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 224
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 224 (accept_3_2 28 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 224 (accept_3_2 25 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 224 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 224
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 224 (accept_3_2 22 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 224 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 224 (accept_3_2 19 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 224 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 224
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 224 (accept_3_2 16 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 224 (accept_3_2 13 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 224 (Polychromatic418967fa.accept_24_12_5_8_1_13359 12 125
  224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 224
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 224 (accept_3_2 10 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 224 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 125 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 224 (accept_3_2 7 125 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 224 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 125 224 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 224
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 224 (accept_3_2 4 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 224 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 224 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 224 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 125 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 224 (accept_3_2 1 125 224 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  224))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_224_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


