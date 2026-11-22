-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch245
-- name    : Polychromatic418967fa_Branch245
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:06.2743+00:00
-- url     : https://prove2.me/theorems/e0fb25d6-cad9-46a8-aea4-12541301cb67
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch245_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_245 : allB 245 245 :=
  allB_succ' 2 244 245 (Eq.refl Bool.true) (allA_of_3_0 2 244 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  243 245 (Eq.refl Bool.true) (allA_succ_of_accept 2 243 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 245 (accept_3_2 1 243 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243 245))) (allB_succ' 4 242 245 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 242 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 242 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 245 (Polychromatic418967fa.accept_19_2_14_17_1_700 2 242
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 242 245 (accept_3_2 1 242 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242 245)))) (allB_succ' 5 241 245 (Eq.refl Bool.true) (allA_of_3_0
  5 241 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 240 245 (Eq.refl Bool.true) (allA_succ_of_gcd 5 240
  245 5 1 48 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4
  240 245 (accept_3_2 4 240 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 240 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 240 245 (Polychromatic418967fa.accept_19_2_12_17_1_5197 2 240 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 245 (accept_3_2 1 240 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 240 245)))))) (allB_succ' 7 239 245 (Eq.refl Bool.true) (allA_succ_of_accept 6 239 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 239 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 239 245 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 239 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 245 (accept_3_2 4 239 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 239 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 239 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  239 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 245 (accept_3_2 1 239
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239 245))))))) (allB_succ' 8 238 245 (Eq.refl Bool.true)
  (allA_of_3_0 8 238 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 237 245 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 237 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 245 (accept_3_2 7 237 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 237 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 237 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 5
  237 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 245 (accept_3_2 4 237
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 245
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 237 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 237 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 245 (accept_3_2 1 237 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 245))))))))) (allB_succ' 10 236 245 (Eq.refl Bool.true) (allA_succ_of_accept 9 236 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 236 245 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 236 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 245 (accept_3_2 7 236 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 236 245 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 236 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 245 (Polychromatic418967fa.accept_14_5_12_7_1_2767
  5 236 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 236 245 (accept_3_2 4
  236 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 236 245
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 236 245 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 236 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 245 (accept_3_2 1 236 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 236 245)))))))))) (allB_succ' 11 235 245 (Eq.refl Bool.true) (allA_of_3_0 11 235 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 234 245 (Eq.refl Bool.true) (allA_succ_of_accept 11 234 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 234 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 234 245 (accept_3_2 10 234 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  234 245 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 234 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 234 245 (Polychromatic418967fa.accept_19_8_6_17_1_5186 8 234 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 245 (accept_3_2 7 234 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 234 245 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 234 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 245
  (Polychromatic418967fa.accept_22_5_14_3_1_14772 5 234 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 234 245 (accept_3_2 4 234 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  234 245 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 234 245 (Polychromatic418967fa.accept_17_2_13_7_1_5011 2 234 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 245 (accept_3_2 1 234 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 234 245)))))))))))) (allB_succ' 13 233 245 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 233 245 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 233 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 245 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 233
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 245 (accept_3_2 10 233
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 245
  (Polychromatic418967fa.accept_21_9_2_14_1_7251 9 233 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 233 245 (Polychromatic418967fa.accept_10_8_3_5_1_613 8 233 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 245 (accept_3_2 7 233 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 233 245 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 233 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 245 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  233 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 245 (accept_3_2 4 233
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 245
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 233 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 233 245 (Polychromatic418967fa.accept_10_2_3_5_1_996 2 233 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 245 (accept_3_2 1 233 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 233 245))))))))))))) (allB_succ' 14 232 245 (Eq.refl Bool.true) (allA_of_3_0 14 232 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 231 245 (Eq.refl Bool.true) (allA_succ_of_gcd 14 231 245 7 2 33 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 231 245
  (accept_3_2 13 231 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 245
  (Polychromatic418967fa.accept_9_3_6_2_1_160 12 231 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 231 245 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 231 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 245 (accept_3_2 10 231 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 231 245 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 231 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 245 (Polychromatic418967fa.accept_6_2_3_5_1_26 8
  231 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 231 245 7 1 33 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 231 245
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 231 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 231 245 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 231 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 245 (accept_3_2 4 231 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 231 245 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 231 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2
  231 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 245 (accept_3_2 1 231
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 245))))))))))))))) (allB_succ' 16 230 245 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 230 245 5 3 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 230 245 (Polychromatic418967fa.accept_13_1_9_11_1_703 14 230 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 245 (accept_3_2 13 230 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 245 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 230 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 230 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 245 5 2 46 49 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 230 245 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 230 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 245 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 230 245
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 245 (accept_3_2 7 230 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 245 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  230 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 230 245 5 1 46 49 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 230 245 (accept_3_2 4
  230 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 245
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 230 245 (Polychromatic418967fa.accept_13_2_9_11_1_258 2 230 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 245 (accept_3_2 1 230 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 230 245)))))))))))))))) (allB_succ' 17 229 245 (Eq.refl Bool.true) (allA_of_3_0 17 229 245
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 228 245 (Eq.refl Bool.true) (allA_succ_of_accept 17 228 245
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 228 245 (accept_3_2 16 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 228 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 228 245 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 228 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 228 245 (accept_3_2 13 228 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 228 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 228 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 245
  (Polychromatic418967fa.accept_14_11_4_7_1_609 11 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 228 245 (accept_3_2 10 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  228 245 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 228 245 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 228 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 245 (accept_3_2 7 228 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 245 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 228 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 245
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 245 (accept_3_2 4 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  228 245 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 228 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 228 245 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 228 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 245 (accept_3_2 1 228 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 228 245)))))))))))))))))) (allB_succ' 19 227 245 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 227 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 227 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 245 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 227
  245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 245 (accept_3_2 16 227
  245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 245
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 227 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 227 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 245 (accept_3_2 13 227 245 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 227 245 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 227 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 245
  (Polychromatic418967fa.accept_14_11_3_7_1_604 11 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 245 (accept_3_2 10 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 245 (Polychromatic418967fa.accept_20_9_7_5_1_2114 9 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 245 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 227 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 245 (accept_3_2 7 227 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 245 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 245
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 245 (accept_3_2 4 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 245 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 227 245 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 245 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 245 (accept_3_2 1 227 245 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 245)))))))))))))))))))
  (Polychromatic418967fa.branch_245_segment_001))))))))))))))))))


