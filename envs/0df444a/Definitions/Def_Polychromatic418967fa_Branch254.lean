-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch254
-- name    : Polychromatic418967fa_Branch254
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:06.708352+00:00
-- url     : https://prove2.me/theorems/74e4607d-3575-493a-af34-d73188b98e31
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch254_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_254 : allB 254 254 :=
  allB_succ' 2 253 254 (Eq.refl Bool.true) (allA_of_3_0 2 253 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  252 254 (Eq.refl Bool.true) (allA_succ_of_gcd 2 252 254 2 1 126 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 254 (accept_3_2 1 252 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 252 254))) (allB_succ' 4 251 254 (Eq.refl Bool.true) (allA_succ_of_accept 3 251 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 251 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 251 254 (Polychromatic418967fa.accept_19_2_4_7_1_10048 2 251 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 254 (accept_3_2 1 251 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 251 254)))) (allB_succ' 5 250 254 (Eq.refl Bool.true) (allA_of_3_0 5 250 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 249 254 (Eq.refl Bool.true) (allA_succ_of_accept 5 249 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 249 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 254 (accept_3_2 4 249 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 249 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 254 (Polychromatic418967fa.accept_23_2_19_1_1_15513 2 249 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 254 (accept_3_2 1 249 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 249 254)))))) (allB_succ' 7 248 254 (Eq.refl Bool.true) (allA_succ_of_gcd 6
  248 254 2 3 124 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 248 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 248 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 248 254 2 2 124 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 248 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  248 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 248 254 2 1 124 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 248 254 (accept_3_2 1
  248 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248 254))))))) (allB_succ' 8 247 254 (Eq.refl Bool.true)
  (allA_of_3_0 8 247 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 246 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 246 254 2 4 123 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 246 254 (accept_3_2 7 246 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 254 2 3 123 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 246 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 254 2 2 123 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 246 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 246 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 246 254 2 1 123 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 246 254 (accept_3_2 1 246 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246
  254))))))))) (allB_succ' 10 245 254 (Eq.refl Bool.true) (allA_succ_of_accept 9 245 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 245 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 245 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 245 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 254 (accept_3_2 7 245 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 245 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 245 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 254 (Polychromatic418967fa.accept_13_5_11_7_1_559
  5 245 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 254 (accept_3_2 4
  245 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 245 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 245 254 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 245 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 254 (accept_3_2 1 245 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 245 254)))))))))) (allB_succ' 11 244 254 (Eq.refl Bool.true) (allA_of_3_0 11 244 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 243 254 (Eq.refl Bool.true) (allA_succ_of_accept 11 243 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 243 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 243 254 (accept_3_2 10 243 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  243 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 243 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 243 254 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 243 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 254 (accept_3_2 7 243 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 243 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 243 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 243 254 (accept_3_2 4 243 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  243 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 243 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 243 254 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 243 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 254 (accept_3_2 1 243 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 243 254)))))))))))) (allB_succ' 13 242 254 (Eq.refl Bool.true) (allA_succ_of_gcd 12 242
  254 2 6 121 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 242 254 (Polychromatic418967fa.accept_19_11_14_7_1_4473 11 242 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 242 254 2 5 121 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 242 254 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 242 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 242 254 2 4 121 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 242 254 (accept_3_2 7 242 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 242 254 2 3 121 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 242 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 242 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 242 254 2 2 121 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 242 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 242 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 242 254 2 1 121 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 242 254 (accept_3_2 1 242 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 242 254))))))))))))) (allB_succ' 14 241 254 (Eq.refl Bool.true) (allA_of_3_0
  14 241 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 240 254 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  240 254 2 7 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 240 254 (accept_3_2 13 240 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  240 254 2 6 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 240 254 (Polychromatic418967fa.accept_19_11_12_7_1_3188 11 240 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 254 2 5 120 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 254
  (Polychromatic418967fa.accept_13_9_6_7_1_551 9 240 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 240 254 2 4 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 240 254 (accept_3_2 7 240 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 240 254 2 3 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 240 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 240 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 240 254 2 2 120 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 240 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 240 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 240 254 2 1 120 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 254 (accept_3_2 1 240 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  254))))))))))))))) (allB_succ' 16 239 254 (Eq.refl Bool.true) (allA_succ_of_accept 15 239 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 239 254 (Polychromatic418967fa.accept_19_14_11_7_1_7236 14 239 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 254 (accept_3_2 13 239 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 239 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 239 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 254
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 254 (accept_3_2 10 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 239 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 254 (accept_3_2 7 239 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 239 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 254 (accept_3_2 4 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 239 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 254 (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 239 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 254 (accept_3_2 1 239 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 254)))))))))))))))) (allB_succ' 17 238 254 (Eq.refl Bool.true) (allA_of_3_0 17 238
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 237 254 (Eq.refl Bool.true) (allA_succ_of_accept 17 237
  254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 237 254 (accept_3_2 16 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 237 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 237 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 237 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 254 (accept_3_2 13 237 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 237 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 237 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 254 (accept_3_2 10 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  237 254 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 237 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 237 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 254 (accept_3_2 7 237 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 237 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 254
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 254 (accept_3_2 4 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  237 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 237 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 237 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 237 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 254 (accept_3_2 1 237 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 237 254)))))))))))))))))) (allB_succ' 19 236 254 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 236 254 2 9 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 236 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 236 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 236 254 2 8 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  236 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 236 254 2 7 118 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 236 254 (accept_3_2 13
  236 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 236 254 2 6 118 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 236 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 236 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 236 254 2 5 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 236 254 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 236 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 236 254 2 4 118 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 236 254 (accept_3_2 7 236 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236 254 2 3 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5
  236 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 254 2 2 118 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 236 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 254 2 1 118 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 254 (accept_3_2 1 236 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  254))))))))))))))))))) (allB_succ' 20 235 254 (Eq.refl Bool.true) (allA_of_3_0 20 235 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 234 254 (Eq.refl Bool.true) (allA_succ_of_gcd 20 234 254 2 10 117 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 254 (accept_3_2 19 234 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 234 254 2 9 117 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 234 254
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 234 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 234 254 2 8 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 234 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 234 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 254 2 7 117 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 254 (accept_3_2 13 234 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 234 254 2 6 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 254
  (Polychromatic418967fa.accept_22_11_14_12_1_7700 11 234 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 234 254 2 5 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 234 254 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 234 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 254 2 4 117 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 254 (accept_3_2 7 234 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 254 2 3 117 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 234 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 254 2 2 117 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 234 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 254 2 1 117 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 254 (accept_3_2 1 234 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 234 254))))))))))))))))))))) (allB_succ' 22 233 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 233 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 233
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 254 (accept_3_2 19 233
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 254
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 233 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 233 254 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 254 (accept_3_2 16 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 233 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 233 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 254 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 233 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 254 (accept_3_2 13
  233 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 233 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 233 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 254 (accept_3_2 10 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 233 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 8
  233 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 254 (accept_3_2 7 233
  254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 233 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 233 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 254 (accept_3_2 4 233 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 233 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 233 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 254 (Polychromatic418967fa.accept_19_2_5_7_1_10021
  2 233 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 254 (accept_3_2 1
  233 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233 254)))))))))))))))))))))) (allB_succ' 23 232 254
  (Eq.refl Bool.true) (allA_of_3_0 23 232 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 231 254 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 231 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 254 (accept_3_2 22 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 231 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 254
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 254 (accept_3_2 19 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 254 (accept_3_2 16 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 254 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 231 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 254 (accept_3_2 13 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 254 (accept_3_2 10 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 231 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 254
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 254 (accept_3_2 7 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 254 (accept_3_2 4 231 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 231 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 254
  (Polychromatic418967fa.accept_25_2_6_4_1_15540 2 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 254 (accept_3_2 1 231 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  254)))))))))))))))))))))))) (allB_succ' 25 230 254 (Eq.refl Bool.true) (allA_succ_of_gcd 24 230 254 2 12 115 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 230 254
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 230 254 2 11 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 230 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 230 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 230 254 2 10 115 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 230 254 (accept_3_2 19 230 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 230 254 2 9 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 230 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  230 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 254 2 8 115 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 230 254 2 7 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 230 254 (accept_3_2 13 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 254 2 6 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 230 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 254 2 5 115 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 254 2 4 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 254 (accept_3_2 7 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 254 2 3 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 254 (Polychromatic418967fa.accept_19_5_2_7_1_1019 5 230 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 254 2 2 115 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 254 2 1 115 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 254 (accept_3_2 1 230 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  254))))))))))))))))))))))))) (allB_succ' 26 229 254 (Eq.refl Bool.true) (allA_of_3_0 26 229 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 228 254 (Eq.refl Bool.true) (allA_succ_of_gcd 26 228 254 2 13 114 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 254 (accept_3_2 25
  228 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 228 254 2 12 114 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 228 254 2 11 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 228 254 (Polychromatic418967fa.accept_18_3_12_2_1_2639 21 228 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 228 254 2 10 114 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 254 (accept_3_2 19 228 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 254 2 9 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 228 254 2 8 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 228 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 228 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 254 2 7 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 254 (accept_3_2 13 228 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 254 2 6 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 254 (Polychromatic418967fa.accept_15_11_3_14_1_971
  11 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 254 2 5 114 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 228 254 2 4 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 228 254 (accept_3_2 7 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 254 2 3 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 228 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 228 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 254 2 2 114 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 228 254
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 3 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 228 254 2 1 114 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 228 254 (accept_3_2 1 228 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  254))))))))))))))))))))))))))) (allB_succ' 28 227 254 (Eq.refl Bool.true) (allA_succ_of_accept 27 227 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 227 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 227 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 254 (accept_3_2 25 227 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 227 254 (Polychromatic418967fa.accept_17_7_6_16_1_2195 24 227 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 254
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 254 (accept_3_2 22 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 227 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 254 (accept_3_2 19 227 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 254 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 227 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 254 (accept_3_2 16 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 254 (Polychromatic418967fa.accept_13_1_6_7_1_550 14 227 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 254 (accept_3_2 13 227 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 227 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 254
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 254 (accept_3_2 10 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 227 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 254 (accept_3_2 7 227 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 227 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 254 (accept_3_2 4 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 227 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 254 (accept_3_2 1 227 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 254)))))))))))))))))))))))))))) (allB_succ' 29 226 254 (Eq.refl Bool.true)
  (allA_of_3_0 29 226 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 225 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 225 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 225 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 254 (accept_3_2 28 225 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 225 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 225 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 254 (Polychromatic418967fa.accept_10_6_5_4_1_571
  26 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 254 (accept_3_2 25
  225 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 225 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 225 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 225 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 254 (accept_3_2 22 225 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 225 254 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 225 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 254
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 254 (accept_3_2 19 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 254 (accept_3_2 16 225 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 225 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 254
  (Polychromatic418967fa.accept_27_14_9_11_1_13552 14 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 225 254 (accept_3_2 13 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 225 254 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 225 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 225 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 254 (accept_3_2 10 225 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 254 (Polychromatic418967fa.accept_10_9_5_4_1_966 9
  225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 254
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 254 (accept_3_2 7 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 254 (accept_3_2 4 225 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 225 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 254
  (Polychromatic418967fa.accept_19_2_16_7_1_11424 2 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 254 (accept_3_2 1 225 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  254)))))))))))))))))))))))))))))) (allB_succ' 31 224 254 (Eq.refl Bool.true) (allA_succ_of_gcd 30 224 254 2 15 112 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 224 254
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 224 254 2 14 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 224 254 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 224 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 224 254 2 13 112 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 224 254 (accept_3_2 25 224 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 224 254 2 12 112 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 224 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 224 254 2 11 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 224 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 224 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 224 254 2 10 112 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 224 254 (accept_3_2 19 224 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 224 254 2 9 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 224 254 (Polychromatic418967fa.accept_12_5_8_2_1_309
  17 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 254 2 8 112 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 254
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 254 2 7 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 254 (accept_3_2 13 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 254 2 6 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 224 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 224 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 254 2 5 112 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 254
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 224 254 2 4 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 224 254 (accept_3_2 7 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 224 254 2 3 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 224 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 224 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 254 2 2 112 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 254 2 1 112 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 254 (accept_3_2 1 224 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  254))))))))))))))))))))))))))))))) (allB_succ' 32 223 254 (Eq.refl Bool.true) (allA_of_3_0 32 223 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 222 254 (Eq.refl Bool.true) (allA_succ_of_gcd 32 222 254 2 16 111 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 254
  (accept_3_2 31 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 222 254 2 15 111 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 222 254
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 222 254 2 14 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 222 254 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 222 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 222 254 2 13 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 254 (accept_3_2 25 222 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 222 254 2 12 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 222 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  222 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 254 2 11 111 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 222 254
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 222 254 2 10 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 222 254 (accept_3_2 19 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 254 2 9 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 222 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 254 2 8 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 222 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 222 254 2 7 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 254 (accept_3_2 13 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 254 2 6 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 222 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 254 2 5 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 222 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 222 254 2 4 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 222 254 (accept_3_2 7 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 254 2 3 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 254 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 222 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 254 2 2 111 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 254
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 254 2 1 111 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 254 (accept_3_2 1 222 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  254))))))))))))))))))))))))))))))))) (allB_succ' 34 221 254 (Eq.refl Bool.true) (allA_succ_of_accept 33 221 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 221 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 221 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 254 (accept_3_2 31 221 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 221 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 221 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 254
  (Polychromatic418967fa.accept_27_2_5_11_1_15539 29 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 221 254 (accept_3_2 28 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 221 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 221 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 221 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 254 (accept_3_2 25 221 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 254 (Polychromatic418967fa.accept_9_6_5_2_1_421
  24 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 221 254 (accept_3_2 22 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 221 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 254 (accept_3_2 19 221 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 254 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 221 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 254 (accept_3_2 16 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 254 (Polychromatic418967fa.accept_19_14_12_7_1_10027 14 221 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 254 (accept_3_2 13 221 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 221 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 221 254 (accept_3_2 10 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  221 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 221 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 221 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 254 (accept_3_2 7 221 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 221 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 254 (accept_3_2 4 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 254 (Polychromatic418967fa.accept_22_2_1_12_1_13867 2 221 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 254 (accept_3_2 1 221 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 221 254)))))))))))))))))))))))))))))))))) (allB_succ' 35 220 254 (Eq.refl
  Bool.true) (allA_of_3_0 35 220 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 219 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 219 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 219 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 254 (accept_3_2 34 219 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 219 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 254 (Polychromatic418967fa.accept_9_5_3_2_1_171
  32 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 254 (accept_3_2 31
  219 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 254
  (Polychromatic418967fa.accept_12_6_3_2_1_743 30 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 219 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 254 (accept_3_2 28 219 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 254 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 219 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 254 (accept_3_2 25 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 254 (accept_3_2 22 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 219 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 254
  (Polychromatic418967fa.accept_11_9_10_1_1_581 20 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 254 (accept_3_2 19 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 254 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 254 (accept_3_2 16 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 219 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 254 (accept_3_2 13 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 254 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 254 (accept_3_2 10 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 219 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 254
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 254 (accept_3_2 7 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 254 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 254 (accept_3_2 4 219 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 254 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 219 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 254
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 254 (accept_3_2 1 219 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  254)))))))))))))))))))))))))))))))))))) (allB_succ' 37 218 254 (Eq.refl Bool.true) (allA_succ_of_gcd 36 218 254 2 18
  109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 218
  254 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 218 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 218 254 2 17 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 218 254 (Polychromatic418967fa.accept_23_10_11_1_1_15538 33 218 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 218 254 2 16 109 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 218 254 (accept_3_2 31
  218 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 218 254 2 15 109 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 218 254
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 218 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 218 254 2 14 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 218 254 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 218 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 218 254 2 13 109 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 218 254 (accept_3_2 25 218 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 218 254 2 12 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 218 254
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 23 218 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 218 254 2 11 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 218 254 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 218 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 218 254 2 10 109 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 218 254 (accept_3_2 19 218 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 218 254 2 9 109 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 218 254
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 218 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 218 254 2 8 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 218 254 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 218 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 218 254 2 7 109 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 218 254 (accept_3_2 13 218 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 218 254 2 6 109 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 218 254
  (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 218 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 218 254 2 5 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 218 254 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 218 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 218 254 2 4 109 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 218 254 (accept_3_2 7 218 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 218 254 2 3 109 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 218 254
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 218 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 218 254 2 2 109 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 218 254 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 218 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 218 254 2 1 109 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 218 254 (accept_3_2 1 218 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 254))))))))))))))))))))))))))))))))))))) (allB_succ' 38 217 254 (Eq.refl
  Bool.true) (allA_of_3_0 38 217 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 216 254 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 216 254 2 19 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 216 254 (accept_3_2 37 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 254 2 18 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 216 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 216 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 254 2 17 108 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 254
  (Polychromatic418967fa.accept_21_12_6_2_1_7950 33 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 216 254 2 16 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 216 254 (accept_3_2 31 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 216 254 2 15 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 216 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 216 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 254 2 14 108 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 254
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 216 254 2 13 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 216 254 (accept_3_2 25 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 254 2 12 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 216 254 (Polychromatic418967fa.accept_13_10_8_7_1_1074 23 216 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 254 2 11 108 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 216 254
  (Polychromatic418967fa.accept_29_21_13_22_1_15537 21 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 216 254 2 10 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 216 254 (accept_3_2 19 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 216 254 2 9 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 216 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 216 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 254 2 8 108 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 216 254 2 7 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 216 254 (accept_3_2 13 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 254 2 6 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 216 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 216 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 254 2 5 108 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 254
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 254 2 4 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 216 254 (accept_3_2 7 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 254 2 3 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 216 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 216 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 254 2 2 108 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 254 2 1 108 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 254 (accept_3_2 1 216 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  254))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 215 254 (Eq.refl Bool.true) (allA_succ_of_accept 39 215 254
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 215 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 215 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 254 (accept_3_2 37 215 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 215 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 254
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 254 (accept_3_2 34 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 215 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 254 (accept_3_2 31 215 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 254 (accept_3_2 28 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 254 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 254 (accept_3_2 25 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 254 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 215 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 254
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 254 (accept_3_2 22 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 254 (accept_3_2 19 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 254 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 215 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 254 (accept_3_2 16 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 215 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 254 (accept_3_2 13 215 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 254
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 254 (accept_3_2 10 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 254 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 254 (accept_3_2 7 215 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 254 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 215 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 254
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 254 (accept_3_2 4 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 254 (Polychromatic418967fa.accept_15_2_5_14_1_61 2 215 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 254 (accept_3_2 1 215 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 254)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 214 254 (Eq.refl
  Bool.true) (allA_of_3_0 41 214 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 213 254 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 213 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 213 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 254 (accept_3_2 40 213 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 254
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 38 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 213 254 (accept_3_2 37 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 213 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 254 (accept_3_2 34 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 213 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 213 254 (accept_3_2 31 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 213 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 213 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 254 (accept_3_2 28 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 213 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 213 254 (accept_3_2 25 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 213 254 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 254 (accept_3_2 22 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 254 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 213 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 254 (accept_3_2 19 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 254 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 254 (accept_3_2 16 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 213 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 254
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 254 (accept_3_2 13 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 254 (accept_3_2 10 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 254 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 213 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 254 (accept_3_2 7 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 254 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 254 (accept_3_2 4 213 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 254
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 2 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 254 (accept_3_2 1 213 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  254)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 212 254 (Eq.refl Bool.true) (allA_succ_of_gcd 42 212 254
  2 21 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  212 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 212 254 2 20 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 212 254 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 212 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 212 254 2 19 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 212 254 (accept_3_2 37 212 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 212 254 2 18 106 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 212 254
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 212 254 2 17 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 212 254 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 212 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 212 254 2 16 106 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 212 254 (accept_3_2 31 212 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 212 254 2 15 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 212 254 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 254 2 14 106 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 254
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 212 254 2 13 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 212 254 (accept_3_2 25 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 212 254 2 12 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 212 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 212 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 254 2 11 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 212 254 2 10 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 212 254 (accept_3_2 19 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 212 254 2 9 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 212 254 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 212 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 254 2 8 106 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 254
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 254 2 7 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 254 (accept_3_2 13 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 254 2 6 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 212 254 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 212 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 254 2 5 106 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 254
  (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 254 2 4 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 212 254 (accept_3_2 7 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 212 254 2 3 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 212 254 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 212 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 254 2 2 106 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 254
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 254 2 1 106 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 254 (accept_3_2 1 212 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  254))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 211 254 (Eq.refl Bool.true) (allA_of_3_0 44 211 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 210 254 (Eq.refl Bool.true) (allA_succ_of_gcd 44 210 254 2 22
  105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210
  254 (accept_3_2 43 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 210 254 2 21 105 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 210 254
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 210 254 2 20 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 210 254 (Polychromatic418967fa.accept_12_3_6_2_1_747 39 210 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 210 254 2 19 105 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 254 (accept_3_2 37 210 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 254 2 18 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 210 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 35
  210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 210 254 2 17 105 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 210 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 210 254 2 16 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 210 254 (accept_3_2 31 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 254 2 15 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 254 (Polychromatic418967fa.accept_19_10_1_7_1_10040 29 210 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 254 2 14 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 210 254 2 13 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 210 254 (accept_3_2 25 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 254 2 12 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 210 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 254 2 11 105 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 254 2 10 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 254 (accept_3_2 19 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 254 2 9 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 254 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 210 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 254 2 8 105 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 210 254
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 210 254 2 7 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 254 (accept_3_2 13 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 254 2 6 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 254 (Polychromatic418967fa.accept_20_11_10_14_1_13955 11 210 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 254 2 5 105 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 254
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 254 2 4 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 254 (accept_3_2 7 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 254 2 3 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 254 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 210 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 254 2 2 105 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 254
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 254 2 1 105 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 254 (accept_3_2 1 210 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  254))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 209 254 (Eq.refl Bool.true) (allA_succ_of_accept 45
  209 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 254 (accept_3_2 43 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 254 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 209
  254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 254
  (Polychromatic418967fa.accept_22_19_11_12_1_15536 41 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 209 254 (accept_3_2 40 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 209 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 209 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 209 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 254 (accept_3_2 37 209 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 254 (accept_3_2 34 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 209 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 254 (accept_3_2 31 209 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 254 (Polychromatic418967fa.accept_21_9_20_2_1_8000 30 209 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 254
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 254 (accept_3_2 28 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 254 (Polychromatic418967fa.accept_20_6_9_14_1_15535 26 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 254 (accept_3_2 25 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 254 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 209 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 254 (accept_3_2 22 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 254 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 254 (accept_3_2 19 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 254 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 209 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 254
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 254 (accept_3_2 16 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 254 (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 254 (accept_3_2 13 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 254 (Polychromatic418967fa.accept_27_12_20_11_1_15534 12
  209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 254
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 254 (accept_3_2 10 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 254 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 254 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 209 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 254 (accept_3_2 7 209 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 254 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 254
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 254 (accept_3_2 4 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 254 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 254 (Polychromatic418967fa.accept_17_2_5_16_1_1264 2 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 254 (accept_3_2 1 209 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 209 254)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 208 254
  (Eq.refl Bool.true) (allA_of_3_0 47 208 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 207 254 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 207 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 254 (accept_3_2 46 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 207 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 254
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 44 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 207 254 (accept_3_2 43 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 207 254 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 254 (accept_3_2 40 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 254 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 207 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 254
  (Polychromatic418967fa.accept_17_4_3_16_1_9483 38 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 254 (accept_3_2 37 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 207 254 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 254 (accept_3_2 34 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 207 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 254 (accept_3_2 31 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 207 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 254 (accept_3_2 28 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 207 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 254
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 254 (accept_3_2 25 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 254 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 254 (accept_3_2 22 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 207 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 254
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 254 (accept_3_2 19 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 254 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 254 (accept_3_2 16 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 254 (Polychromatic418967fa.accept_19_15_17_7_1_8734 15 207 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 254
  (Polychromatic418967fa.accept_26_14_25_20_1_15533 14 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 207 254 (accept_3_2 13 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 207 254 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 207 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 254 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 254
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 254 (accept_3_2 10 207 254
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 254
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 254 (accept_3_2 7 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 254 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 254 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 254 (accept_3_2 4 207 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 254 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 207 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 254
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 254 (accept_3_2 1 207 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  254)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 206 254 (Eq.refl Bool.true) (allA_succ_of_gcd 48
  206 254 2 24 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 206 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 206 254 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 254 2 23 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 45
  206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 206 254 2 22 103 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 206 254
  (accept_3_2 43 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 206 254 2 21 103 127 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 206 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 206 254 2 20 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 206 254 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 206 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 206 254 2 19 103 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 206 254 (accept_3_2 37 206 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 206 254 2 18 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 206 254 (Polychromatic418967fa.accept_10_5_6_4_1_64 35
  206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 254 2 17 103 127
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 254
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 254 2 16 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 254 (accept_3_2 31 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 254 2 15 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 254 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 206 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 254 2 14 103 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 254
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 254 2 13 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 254 (accept_3_2 25 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 254 2 12 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 254 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 206 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 254 2 11 103 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 254 2 10 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 254 (accept_3_2 19 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 254 2 9 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 254 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 206 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 254 2 8 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 254
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 254 2 7 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 254 (accept_3_2 13 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 254 2 6 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 254 (Polychromatic418967fa.accept_20_11_6_14_1_2621 11 206 254 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 254 2 5 103 127 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 254
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 254 2 4 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 254 (accept_3_2 7 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 254 2 3 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 254 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 206 254 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 254 2 2 103 127 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 254
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 254 2 1 103 127 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 254 (accept_3_2 1 206 254 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  254)))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_254_segment_001))))))))))))))))))))))))))))))))))))))))))))))))


