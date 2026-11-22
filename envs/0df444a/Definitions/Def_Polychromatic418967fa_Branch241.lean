-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch241
-- name    : Polychromatic418967fa_Branch241
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:56.747469+00:00
-- url     : https://prove2.me/theorems/2e70de3e-aedf-4257-a8ee-a8fc7f979bca
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch241_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_241 : allB 241 241 :=
  allB_succ' 2 240 241 (Eq.refl Bool.true) (allA_succ_of_accept 1 240 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  240 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 241)) (allB_succ' 3 239 241
  (Eq.refl Bool.true) (allA_of_3_1 3 239 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 238 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 238 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 238 241 (accept_3_3 2 238 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 238 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 238 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 238 241)))) (allB_succ' 5 237 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 237 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 237 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 237 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 241 (accept_3_3 2 237 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  237 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 241))))) (allB_succ' 6 236 241
  (Eq.refl Bool.true) (allA_of_3_1 6 236 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 235 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 235 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 235 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 241 (accept_3_3 5 235 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 235 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 235 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 241 (accept_3_3 2 235 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 235 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 241))))))) (allB_succ' 8 234 241 (Eq.refl Bool.true) (allA_succ_of_accept 7 234 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 234 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 234 241 (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 234 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 241 (accept_3_3 5 234 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 234 241 (Polychromatic418967fa.accept_17_4_13_3_1_7166 4 234 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 234 241 (accept_3_3 2 234 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  234 241 (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 234 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 234 241)))))))) (allB_succ' 9 233 241 (Eq.refl Bool.true) (allA_of_3_1 9 233 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 232 241 (Eq.refl Bool.true) (allA_succ_of_accept 9 232 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 232 241 (accept_3_3 8 232 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  232 241 (Polychromatic418967fa.accept_16_7_8_1_1_3061 7 232 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 232 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 232 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 241 (accept_3_3 5 232 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 232 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 232 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 232 241 (accept_3_3 2 232 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  232 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 232 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 232 241)))))))))) (allB_succ' 11 231 241 (Eq.refl Bool.true) (allA_succ_of_accept 10 231 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 231 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 231 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 231 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 241 (accept_3_3 8 231 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 231 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 231 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  231 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 241 (accept_3_3 5 231
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 241 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 231 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 231 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 241 (accept_3_3 2 231 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  231 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 231 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 241))))))))))) (allB_succ' 12 230 241 (Eq.refl Bool.true) (allA_of_3_1 12 230 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 229 241 (Eq.refl Bool.true) (allA_succ_of_accept 12 229 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 229 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 241 (accept_3_3 11 229 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 229 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 229 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 241 (accept_3_3 8 229 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 241 (Polychromatic418967fa.accept_19_7_1_13_1_4861 7 229 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 229 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 241 (accept_3_3 5 229 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 229 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 229 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 241 (accept_3_3 2 229 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 229 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 241))))))))))))) (allB_succ' 14 228 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 228 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 228 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 228 241
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 228 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 228 241 (accept_3_3 11 228 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 228 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 228 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 228 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 228 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 241 (accept_3_3 8 228 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 241 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 228 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 228 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 228 241 (accept_3_3 5 228 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  228 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 228 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 228 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 228 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 241 (accept_3_3 2 228 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 228 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 241)))))))))))))) (allB_succ' 15 227 241 (Eq.refl
  Bool.true) (allA_of_3_1 15 227 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 226 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 226 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 226 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 241 (accept_3_3 14 226 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 226 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 226 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 241 (Polychromatic418967fa.accept_7_5_2_3_1_106
  12 226 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 226 241 (accept_3_3 11
  226 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 226 241
  (Polychromatic418967fa.accept_22_10_6_21_1_8302 10 226 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 226 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 241 (accept_3_3 8 226 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 226 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 226 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 241 (accept_3_3 5 226 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 226 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 241 (accept_3_3 2 226 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 226 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 241)))))))))))))))) (allB_succ' 17 225 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 225 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 241 (Polychromatic418967fa.accept_11_4_5_10_1_926
  15 225 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 241 (accept_3_3 14
  225 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 241
  (Polychromatic418967fa.accept_17_13_4_3_1_1446 13 225 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 225 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 225 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 241 (accept_3_3 11 225 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 225 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 225 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  225 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 241 (accept_3_3 8 225
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 241
  (Polychromatic418967fa.accept_17_7_4_3_1_3456 7 225 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 225 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 225 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 241 (accept_3_3 5 225 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 225 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  225 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 241 (accept_3_3 2 225
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 241
  (Polychromatic418967fa.accept_19_1_16_13_1_10571 1 225 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 241))))))))))))))))) (allB_succ' 18 224 241 (Eq.refl Bool.true) (allA_of_3_1 18 224 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 223 241 (Eq.refl Bool.true) (allA_succ_of_accept 18 223 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 223 241 (accept_3_3 17 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 223 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 241 (Polychromatic418967fa.accept_19_15_14_13_1_2343 15 223 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 241 (accept_3_3 14 223 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 241 (Polychromatic418967fa.accept_20_13_3_1_1_3065 13 223
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 241
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 241 (accept_3_3 11 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 223 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 241 (accept_3_3 8 223 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 223 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 241 (accept_3_3 5 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 223 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 241 (Polychromatic418967fa.accept_15_3_13_1_1_479 3 223 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 241 (accept_3_3 2 223 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 241 (Polychromatic418967fa.accept_17_1_2_3_1_4668 1 223 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 241))))))))))))))))))) (allB_succ' 20 222 241
  (Eq.refl Bool.true) (allA_succ_of_accept 19 222 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 222 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 222 241
  (Polychromatic418967fa.accept_24_18_6_1_1_11229 18 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 241 (accept_3_3 17 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 222 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 222 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 222 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 241 (accept_3_3 14 222 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 241 (Polychromatic418967fa.accept_9_4_6_7_1_286
  13 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 222 241 (accept_3_3 11 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 222 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 222 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 222 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 241 (accept_3_3 8 222 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 222 241 (accept_3_3 5 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  222 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 222 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 222 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 241 (accept_3_3 2 222 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 222 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 241)))))))))))))))))))) (allB_succ' 21 221 241
  (Eq.refl Bool.true) (allA_of_3_1 21 221 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 220 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 220 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 220 241 (accept_3_3 20 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 220 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 220 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 220 241
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 220 241 (accept_3_3 17 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 220 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 220 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 220 241 (accept_3_3 14 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 220 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 220 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 220 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 220 241 (accept_3_3 11 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 220 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 220 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 241 (accept_3_3 8 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 220 241 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 220 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 220 241 (accept_3_3 5 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  220 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 220 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 220 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 241 (accept_3_3 2 220 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 220 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 241)))))))))))))))))))))) (allB_succ' 23 219 241
  (Eq.refl Bool.true) (allA_succ_of_accept 22 219 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 219 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 219 241 (accept_3_3 20 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 219 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 219 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 219 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 241 (accept_3_3 17 219 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 219 241 (accept_3_3 14 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 219 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 219 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 219 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 241 (accept_3_3 11 219 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 219 241 (accept_3_3 8 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  219 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 219 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 241 (accept_3_3 5 219 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 241
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 241 (accept_3_3 2 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 219 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 241))))))))))))))))))))))) (allB_succ' 24 218 241 (Eq.refl Bool.true) (allA_of_3_1 24 218
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 217 241 (Eq.refl Bool.true) (allA_succ_of_accept 24 217
  241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 217 241 (accept_3_3 23 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 217 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 217 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 217 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 241 (accept_3_3 20 217 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430
  19 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 241
  (Polychromatic418967fa.accept_14_4_7_3_1_1718 18 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 241 (accept_3_3 17 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 217 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 241 (accept_3_3 14 217 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 217 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 241 (accept_3_3 11 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 241 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 217 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 241 (accept_3_3 8 217 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 241 (Polychromatic418967fa.accept_22_7_19_21_1_14539 7 217 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 241 (accept_3_3 5 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 217 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 241 (accept_3_3 2 217 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 241 (Polychromatic418967fa.accept_19_1_8_13_1_4875 1 217 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 241))))))))))))))))))))))))) (allB_succ' 26 216 241
  (Eq.refl Bool.true) (allA_succ_of_accept 25 216 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 216 241
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 216 241 (accept_3_3 23 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 216 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 216 241 (Polychromatic418967fa.accept_19_2_7_13_1_2337 21 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 241 (accept_3_3 20 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 241 (Polychromatic418967fa.accept_22_19_18_21_1_14538 19
  216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 216 241 (accept_3_3 17 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 216 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 216 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 241 (accept_3_3 14 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 241 (Polychromatic418967fa.accept_23_13_9_11_1_4514 13 216
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 241
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 216 241 (accept_3_3 11 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 216 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 216 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 216 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 241 (accept_3_3 8 216 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 241
  (Polychromatic418967fa.accept_19_6_7_13_1_2289 6 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 216 241 (accept_3_3 5 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  216 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 216 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 216 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 216 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 241 (accept_3_3 2 216 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 216 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 241)))))))))))))))))))))))))) (allB_succ' 27 215 241
  (Eq.refl Bool.true) (allA_of_3_1 27 215 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 214 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 214 241 (accept_3_3 26 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 214 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 214 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 214 241
  (Polychromatic418967fa.accept_17_7_10_3_1_1421 24 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 214 241 (accept_3_3 23 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 214 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 214 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 241 (accept_3_3 20 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 214 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 241
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 241 (accept_3_3 17 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 241 (accept_3_3 14 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 214 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 241
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 241 (accept_3_3 11 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 241 (Polychromatic418967fa.accept_19_10_5_13_1_6287 10 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 241 (accept_3_3 8 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 241 (accept_3_3 5 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 214 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 241 (accept_3_3 2 214 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 214 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214 241)))))))))))))))))))))))))))) (allB_succ' 29 213
  241 (Eq.refl Bool.true) (allA_succ_of_accept 28 213 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 213 241 (accept_3_3 26 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 213 241 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 213 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 241 (accept_3_3 23 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 213 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 241 (accept_3_3 20 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 241 (accept_3_3 17 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 241 (accept_3_3 14 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 213 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 241 (accept_3_3 11 213 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 241
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 241 (accept_3_3 8 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 241 (Polychromatic418967fa.accept_19_7_4_13_1_6319 7 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 213 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 241 (accept_3_3 5 213 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 241 (accept_3_3 2 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 213 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 241))))))))))))))))))))))))))))) (allB_succ' 30 212 241 (Eq.refl Bool.true) (allA_of_3_1 30
  212 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 211 241 (Eq.refl Bool.true) (allA_succ_of_accept 30
  211 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 211 241 (accept_3_3 29 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 211 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 211
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 241 (accept_3_3 26 211
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 211 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 241 (accept_3_3 23 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 211 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 211 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 21
  211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 241 (accept_3_3 20
  211 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 211 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 241 (accept_3_3 17 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 211 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 211 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 241 (Polychromatic418967fa.accept_9_6_4_7_1_300
  15 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 241 (accept_3_3 14
  211 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 241
  (Polychromatic418967fa.accept_16_13_3_1_1_2100 13 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 211 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 241 (accept_3_3 11 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 211 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9
  211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 241 (accept_3_3 8 211
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 241
  (Polychromatic418967fa.accept_19_7_2_13_1_4935 7 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 211 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 241 (accept_3_3 5 211 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 211 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 211 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 241 (accept_3_3 2 211
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 241 (Polychromatic418967fa.accept_9_1_4_7_1_7
  1 211 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211
  241))))))))))))))))))))))))))))))) (allB_succ' 32 210 241 (Eq.refl Bool.true) (allA_succ_of_accept 31 210 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 210 241 (Polychromatic418967fa.accept_22_8_12_21_1_11444 30 210 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 210 241 (accept_3_3 29 210 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 210 241 (accept_3_3 26 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 210 241 (Polychromatic418967fa.accept_16_9_2_1_1_3077 25 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 210 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 210 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 241 (accept_3_3 23 210 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 241
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 210 241 (accept_3_3 20 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 210 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 210 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 241 (accept_3_3 17 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 241 (Polychromatic418967fa.accept_19_16_1_13_1_4860 16 210
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 210 241 (accept_3_3 14 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 210 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 210 241 (Polychromatic418967fa.accept_16_12_2_1_1_1215 12 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 241 (accept_3_3 11 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 210 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 241
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 210 241 (accept_3_3 8 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  210 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 210 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 210 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 241 (accept_3_3 5 210 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 210 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 210 241 (accept_3_3 2 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  210 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 210 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 241)))))))))))))))))))))))))))))))) (allB_succ' 33 209 241 (Eq.refl Bool.true) (allA_of_3_1
  33 209 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 208 241 (Eq.refl Bool.true) (allA_succ_of_accept 33
  208 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 208 241 (accept_3_3 32 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 208 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 208 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 208 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 208 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 241 (accept_3_3 29 208 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 241
  (Polychromatic418967fa.accept_19_9_18_13_1_4931 28 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 208 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 208 241 (accept_3_3 26 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 208 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 208 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 208 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 208 241 (accept_3_3 23 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 208 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 208 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 208 241 (accept_3_3 20 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 208 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 208 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 208 241
  (Polychromatic418967fa.accept_15_3_13_1_1_479 18 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 208 241 (accept_3_3 17 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 208 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 208 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 241 (accept_3_3 14 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 208 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 208 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 208 241 (accept_3_3 11 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 208 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 208 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 241 (accept_3_3 8 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 241 (Polychromatic418967fa.accept_17_7_4_3_1_3456 7 208 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 241 (accept_3_3 5 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 208 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 241 (accept_3_3 2 208 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 208 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 241)))))))))))))))))))))))))))))))))) (allB_succ' 35
  207 241 (Eq.refl Bool.true) (allA_succ_of_accept 34 207 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 207 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 207 241 (accept_3_3 32 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 207 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 207 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 207 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 241 (accept_3_3 29 207 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 207 241 (accept_3_3 26 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 207 241 (Polychromatic418967fa.accept_19_6_17_13_1_2323 25 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 207 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 241 (accept_3_3 23 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 207 241 (accept_3_3 20 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 207 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 207 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 241 (accept_3_3 17 207 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 207 241 (accept_3_3 14 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 207 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 241 (accept_3_3 11 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 241 (accept_3_3 8 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 241 (accept_3_3 5 207 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 241
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 241 (accept_3_3 2 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 207 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 241))))))))))))))))))))))))))))))))))) (allB_succ' 36 206 241 (Eq.refl Bool.true)
  (allA_of_3_1 36 206 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 205 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 205 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 205 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 241 (accept_3_3 35 205 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 205 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 241 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 241 (accept_3_3 32
  205 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 241
  (Polychromatic418967fa.accept_24_7_13_1_1_9522 31 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 205 241 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 205 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 241 (accept_3_3 29 205 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 205 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 241 (Polychromatic418967fa.accept_7_6_2_3_1_107
  27 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 241 (accept_3_3 26
  205 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 205 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 205 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 241 (accept_3_3 23 205 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 205 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 241
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 241 (accept_3_3 20 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 241 (Polychromatic418967fa.accept_27_18_16_25_1_14525 18 205 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 241 (accept_3_3 17 205 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 205
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 241 (accept_3_3 14 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 241 (accept_3_3 11 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 241 (Polychromatic418967fa.accept_20_10_5_1_1_4406 10 205 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 241 (accept_3_3 8 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 241 (accept_3_3 5 205 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 205 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 241 (accept_3_3 2 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 205 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 241))))))))))))))))))))))))))))))))))))) (allB_succ' 38 204 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 204 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 204 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 241 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 204
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 204 241 (accept_3_3 35 204
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 204 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 34 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 204 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 204 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 241 (accept_3_3 32 204 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 204 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 241 (Polychromatic418967fa.accept_7_2_1_3_1_102
  30 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 204 241 (accept_3_3 29
  204 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 204 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 204 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 241 (accept_3_3 26 204 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 204 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 241
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 204 241 (accept_3_3 23 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 204 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 204 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 241 (accept_3_3 20 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 204 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 241 (accept_3_3 17 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 204 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 241 (accept_3_3 14 204 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 204 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 241 (accept_3_3 11 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 241 (accept_3_3 8 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 204 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 241
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 241 (accept_3_3 5 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 204 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 241 (accept_3_3 2 204 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 204 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 241))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 203 241 (Eq.refl Bool.true) (allA_of_3_1 39 203 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 202 241 (Eq.refl Bool.true) (allA_succ_of_accept 39 202 241 (Polychromatic418967fa.accept_4_3_2_1_1_50
  39 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 202 241 (accept_3_3 38
  202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 202 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 202 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 202 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 202 241 (accept_3_3 35 202 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 202 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 34 202 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 202 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 202 241 (accept_3_3 32 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 202 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 202 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 202 241 (accept_3_3 29 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 202 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 202 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 202 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 202 241 (accept_3_3 26 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 202 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 202 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 202 241 (accept_3_3 23 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 202 241 (Polychromatic418967fa.accept_19_3_12_13_1_2292 22 202 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 202 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 202 241 (accept_3_3 20 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 202 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 202 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 202 241 (accept_3_3 17 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 202 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 202 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 202 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 202 241 (accept_3_3 14 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 202 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 202 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 202 241 (accept_3_3 11 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 202 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 202 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 202 241 (accept_3_3 8 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  202 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 202 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 202 241 (accept_3_3 5 202 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 202 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 202 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 202 241 (accept_3_3 2 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  202 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 202 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 202 241)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 201 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 201
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 241 (accept_3_3 38 201
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 201 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 241 (accept_3_3 35 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 201 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 241 (Polychromatic418967fa.accept_9_6_3_7_1_580
  33 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 241 (accept_3_3 32
  201 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 201 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 241 (accept_3_3 29 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 241 (Polychromatic418967fa.accept_12_3_9_1_1_290
  27 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 241 (accept_3_3 26
  201 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 241
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 201 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 241 (accept_3_3 23 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 201 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 241 (Polychromatic418967fa.accept_16_5_9_1_1_2070
  21 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 241 (accept_3_3 20
  201 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 201 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 241 (accept_3_3 17 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 241 (Polychromatic418967fa.accept_7_1_5_3_1_268
  15 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 241 (accept_3_3 14
  201 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 241
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 201 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 241 (accept_3_3 11 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 201 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9
  201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 241 (accept_3_3 8 201
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 241
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 201 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 241 (accept_3_3 5 201 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 201 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 241 (accept_3_3 2 201
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 201 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 201 241))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 200 241 (Eq.refl Bool.true) (allA_of_3_1 42
  200 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 199 241 (Eq.refl Bool.true) (allA_succ_of_accept 42
  199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 199 241 (accept_3_3 41 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 199 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 199 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 199 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 241 (accept_3_3 38 199 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 241
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 199 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 199 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 241 (accept_3_3 35 199 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 241 (Polychromatic418967fa.accept_9_6_1_7_1_577
  33 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 241 (accept_3_3 32
  199 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 241
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 199 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 241 (accept_3_3 29 199 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 199 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 199 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 241
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 199 241 (accept_3_3 26 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 199 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 199 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 241 (accept_3_3 23 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 199 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 241 (accept_3_3 20 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 241 (accept_3_3 17 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 199 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 241 (accept_3_3 14 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 241 (accept_3_3 11 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 241
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 241 (accept_3_3 8 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 241 (accept_3_3 5 199 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 199 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 241 (accept_3_3 2 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 241 (Polychromatic418967fa.accept_25_1_24_16_1_14537 1 199 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 241))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 198 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 198 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 198 241 (Polychromatic418967fa.accept_19_4_8_13_1_7802 42 198
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 198 241 (accept_3_3 41 198
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 198 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 198 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 198 241 (accept_3_3 38 198 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 198 241 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 198 241 (accept_3_3 35 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 198 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 198 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 241 (accept_3_3 32 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 241
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 198 241 (accept_3_3 29 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 198 241 (Polychromatic418967fa.accept_15_13_3_1_1_3740 28 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 241 (accept_3_3 26 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 241 (Polychromatic418967fa.accept_19_6_8_13_1_14496 25 198 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 241
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 198 241 (accept_3_3 23 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 198 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 198 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 241 (accept_3_3 20 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 198 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 241
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 241 (accept_3_3 17 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 241 (Polychromatic418967fa.accept_20_16_18_1_1_8836 16 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 241 (accept_3_3 14 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 198 241 (accept_3_3 11 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 198 241 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 198 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 241 (accept_3_3 8 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 241 (accept_3_3 5 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 198 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 241 (accept_3_3 2 198 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 198 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 241))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 197 241 (Eq.refl Bool.true) (allA_of_3_1 45 197 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 196 241 (Eq.refl Bool.true) (allA_succ_of_accept 45 196 241 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 196 241 (accept_3_3 44
  196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 196 241
  (Polychromatic418967fa.accept_21_1_7_10_1_2596 43 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 196 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 196 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 196 241 (accept_3_3 41 196 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 196 241 (Polychromatic418967fa.accept_16_8_4_1_1_2102 40 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 196 241 (accept_3_3 38 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 196 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 196 241 (Polychromatic418967fa.accept_19_17_6_13_1_6334 36 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 196 241 (accept_3_3 35 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 196 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 196
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 196 241 (accept_3_3 32 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 196 241 (Polychromatic418967fa.accept_19_12_6_13_1_2305 31 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 196 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 196 241 (accept_3_3 29 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 196 241 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 196
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 196 241 (accept_3_3 26 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 196 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 196 241 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 196 241 (accept_3_3 23 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 196 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 196
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 196 241 (accept_3_3 20 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 196 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 196 241 (Polychromatic418967fa.accept_17_1_9_3_1_7161 18 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 241 (accept_3_3 17 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 196
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 196 241 (accept_3_3 14 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 196 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 196 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 241 (accept_3_3 11 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 196 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 196
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 196 241 (accept_3_3 8 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  196 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 196 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 196 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 241 (accept_3_3 5 196 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 241 (Polychromatic418967fa.accept_18_4_16_7_1_1873 4 196 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 196 241 (accept_3_3 2 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  196 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 196 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 196 241)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 195 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 195
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 241 (accept_3_3 44 195
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 241
  (Polychromatic418967fa.accept_24_19_3_1_1_5907 43 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 241 (accept_3_3 41 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 195 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 241 (Polychromatic418967fa.accept_7_4_6_3_1_271
  39 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 241 (accept_3_3 38
  195 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 195 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 241 (accept_3_3 35 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 241 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 241 (accept_3_3 32
  195 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 241 (accept_3_3 29 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 195 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 241
  (Polychromatic418967fa.accept_19_8_5_13_1_7800 27 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 241 (accept_3_3 26 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 195 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 195 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 195 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 241 (accept_3_3 23 195 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 195 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 241 (accept_3_3 20 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 241 (accept_3_3 17 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 241
  (Polychromatic418967fa.accept_21_15_6_10_1_10016 15 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 241 (accept_3_3 14 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 195 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 195 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 241 (accept_3_3 11 195 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 241 (accept_3_3 8 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 241 (Polychromatic418967fa.accept_19_7_5_13_1_3493 7 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 241 (accept_3_3 5 195 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 241 (accept_3_3 2 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 195 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 241))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 194 241 (Eq.refl
  Bool.true) (allA_of_3_1 48 194 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 193 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 193 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 193 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 193 241 (accept_3_3 47 193 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 193 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 193 241
  (Polychromatic418967fa.accept_19_7_3_13_1_3492 45 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 193 241 (accept_3_3 44 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 193 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 193 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 193 241 (accept_3_3 41 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 193 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 193 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 193 241 (accept_3_3 38 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 193 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 193 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 241 (accept_3_3 35 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 193 241 (accept_3_3 32 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 193 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 193 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 241 (accept_3_3 29 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 241 (accept_3_3 26 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 241 (accept_3_3 23 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 241 (accept_3_3 20 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 241 (accept_3_3 17 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 16 193
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 241 (accept_3_3 14 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 241 (accept_3_3 11 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 241
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 241 (accept_3_3 8 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 241 (accept_3_3 5 193 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 193 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 241 (accept_3_3 2 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 241))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 192 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 192 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 192 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 192 241 (Polychromatic418967fa.accept_11_4_5_10_1_926
  48 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 192 241 (accept_3_3 47
  192 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 241
  (Polychromatic418967fa.accept_9_1_3_7_1_6 46 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 192 241 (Polychromatic418967fa.accept_19_7_2_13_1_4935 45 192 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 241 (accept_3_3 44 192 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 192 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 192 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 192 241 (accept_3_3 41 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 192 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 192 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 241 (accept_3_3 38 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 192 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 192 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 192 241 (accept_3_3 35 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 192 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 192 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 192 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 241 (accept_3_3 32 192 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 241
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 192 241 (accept_3_3 29 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 192 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 192 241 (Polychromatic418967fa.accept_14_13_10_3_1_1037 27 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 241 (accept_3_3 26 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 241 (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 192
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 192 241 (accept_3_3 23 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 192 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 192 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 241 (accept_3_3 20 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 192 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 241
  (Polychromatic418967fa.accept_21_18_3_10_1_8534 18 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 192 241 (accept_3_3 17 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 192 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 192 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 192 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 241 (accept_3_3 14 192 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  13 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 241
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 192 241 (accept_3_3 11 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 192 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 192 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 241 (accept_3_3 8 192 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 241 (Polychromatic418967fa.accept_14_7_10_3_1_1034
  7 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 192 241 (accept_3_3 5 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  192 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 192 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 192 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 192 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 241 (accept_3_3 2 192 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 192 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  241)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 191 241 (Eq.refl Bool.true) (allA_of_3_1 51 191
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 190 241 (Eq.refl Bool.true) (allA_succ_of_accept 51 190
  241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 190 241 (accept_3_3 50 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 190 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 190 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 190 241 (accept_3_3 47 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 190 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 190 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 190 241 (accept_3_3 44 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 190 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 190 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 190 241 (accept_3_3 41 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 190 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 190 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 190 241 (accept_3_3 38 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 190 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 190 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 190 241 (accept_3_3 35 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 190 241 (Polychromatic418967fa.accept_20_14_10_1_1_13086 34
  190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 190 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 190 241 (accept_3_3 32 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 190 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 190 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 190 241 (accept_3_3 29 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 190 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 190 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 190 241 (accept_3_3 26 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 190 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 190 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 190 241 (accept_3_3 23 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 190 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 190 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 190 241 (accept_3_3 20 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 190 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 190 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 190 241 (accept_3_3 17 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 190 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 190 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 190 241 (accept_3_3 14 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 190 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 190 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 190 241 (accept_3_3 11 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 190 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 10 190 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 190 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 190 241 (accept_3_3 8 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  190 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 190 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 190 241 (accept_3_3 5 190 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 190 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 190 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 190 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 190 241 (accept_3_3 2 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  190 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 190 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 190 241)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 189 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 189 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 241 (Polychromatic418967fa.accept_12_3_9_1_1_290
  51 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 241 (accept_3_3 50
  189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 241
  (Polychromatic418967fa.accept_25_24_14_16_1_14536 49 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 189 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 241 (accept_3_3 47 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 189 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 189 241 (accept_3_3 44 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 189 241 (Polychromatic418967fa.accept_19_5_18_13_1_9116 43 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 189 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 241 (accept_3_3 41 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 189 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 189 241 (accept_3_3 38 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 189 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 37 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 189 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 241 (accept_3_3 35 189 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 241
  (Polychromatic418967fa.accept_19_14_18_13_1_7823 33 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 241 (accept_3_3 32 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 241 (Polychromatic418967fa.accept_17_14_2_3_1_7172 31 189 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 241 (Polychromatic418967fa.accept_16_14_13_1_1_5278 30 189
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 241 (accept_3_3 29 189
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 241
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 189 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 189 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 241 (accept_3_3 26 189 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 189 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 241
  (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 241 (accept_3_3 23 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 241 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 241 (accept_3_3 20 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 241 (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 189
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 241
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 189 241 (accept_3_3 17 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 189 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 241 (accept_3_3 14 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 241 (Polychromatic418967fa.accept_24_13_21_1_1_7730 13 189
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 189 241 (accept_3_3 11 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 189 241 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 241 (accept_3_3 8 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 189 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 241
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 6 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 241 (accept_3_3 5 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 189 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 241 (accept_3_3 2 189 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 189 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  241))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 188 241 (Eq.refl Bool.true) (allA_of_3_1 54
  188 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 187 241 (Eq.refl Bool.true) (allA_succ_of_accept 54
  187 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 187 241 (accept_3_3 53 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 187 241 (Polychromatic418967fa.accept_19_14_16_13_1_3488 52 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 187 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 51
  187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 241 (accept_3_3 50
  187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 241
  (Polychromatic418967fa.accept_19_11_16_13_1_4853 49 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 187 241 (Polychromatic418967fa.accept_19_10_16_13_1_3471 48 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 241 (accept_3_3 47 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 187 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 241
  (Polychromatic418967fa.accept_22_1_11_21_1_6612 45 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 187 241 (accept_3_3 44 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 187 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 187 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 241 (accept_3_3 41 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 241
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 187 241 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 187 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 241 (accept_3_3 38 187 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 187 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 241 (Polychromatic418967fa.accept_7_1_5_3_1_268
  36 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 241 (accept_3_3 35
  187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 187 241 (Polychromatic418967fa.accept_19_14_16_13_1_3488 33 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 241 (accept_3_3 32 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 241 (Polychromatic418967fa.accept_16_15_11_1_1_7767 31 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 241 (accept_3_3 29 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 241 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 241 (Polychromatic418967fa.accept_24_3_19_1_1_9509 27 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 241 (accept_3_3 26 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 241 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 187
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 241
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 241 (accept_3_3 23 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 241 (Polychromatic418967fa.accept_15_6_7_1_1_93 21 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 241 (accept_3_3 20 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 241 (Polychromatic418967fa.accept_22_19_11_21_1_11454 19 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 241 (accept_3_3 17 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 241 (accept_3_3 14 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 241 (Polychromatic418967fa.accept_24_13_19_1_1_11204 13 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 241
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 241 (accept_3_3 11 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 241 (accept_3_3 8 187 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 241 (Polychromatic418967fa.accept_21_7_19_10_1_8567 7 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 241 (accept_3_3 5 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 187 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 241 (Polychromatic418967fa.accept_19_3_16_13_1_2293 3 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 241 (accept_3_3 2 187 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 186 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 186 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 54 186
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 186 241 (accept_3_3 53 186
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 186 241
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 241 (accept_3_3 50 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 186 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 186 241 (Polychromatic418967fa.accept_7_6_4_3_1_266
  48 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 186 241 (accept_3_3 47
  186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 186 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 241 (accept_3_3 44 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  42 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 186 241 (accept_3_3 41
  186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 241 (accept_3_3 38 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 186 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 241 (accept_3_3 35
  186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 186 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 241 (accept_3_3 32 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 241 (Polychromatic418967fa.accept_9_3_6_7_1_562
  30 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 241 (accept_3_3 29
  186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 241 (accept_3_3 26 186 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 186 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 186 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 241
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 186 241 (accept_3_3 23 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 186 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 186 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 241 (accept_3_3 20 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 186 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 186 241 (accept_3_3 17 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 186 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 241 (accept_3_3 14 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 186 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 241 (accept_3_3 11 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 241 (accept_3_3 8 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 241 (accept_3_3 5 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 186 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 241 (accept_3_3 2 186 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 186 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 185 241 (Eq.refl Bool.true) (allA_of_3_1 57
  185 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 184 241 (Eq.refl Bool.true) (allA_succ_of_accept 57
  184 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 184 241 (accept_3_3 56 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 184 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 184 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 184 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 184 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 184 241 (accept_3_3 53 184 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 184 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257
  52 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 184 241 (accept_3_3 50 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 184 241 (Polychromatic418967fa.accept_17_15_14_3_1_5947 49 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 184 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 184 241 (accept_3_3 47 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 184 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 184 241 (accept_3_3 44 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 184 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 184 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 184 241 (accept_3_3 41 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 184 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 184 241 (accept_3_3 38 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 184 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 184 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 184 241 (accept_3_3 35 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 184 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 184 241 (accept_3_3 32 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 184 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 184 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 184 241 (accept_3_3 29 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 184 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 184 241 (accept_3_3 26 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 184 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 184 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 241 (accept_3_3 23 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 184 241 (accept_3_3 20 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 184 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 184 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 241 (accept_3_3 17 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 16 184
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 241 (accept_3_3 14 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 241 (accept_3_3 11 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 241 (accept_3_3 8 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 241 (accept_3_3 5 184 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 184 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 241 (accept_3_3 2 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 183 241
  (Eq.refl Bool.true) (allA_succ_of_accept 58 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 183 241 (accept_3_3 56 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 183 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 241 (accept_3_3 53 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 183 241 (accept_3_3 50 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 183 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 183 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 241 (accept_3_3 47 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 183 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 183 241 (accept_3_3 44 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 183 241 (Polychromatic418967fa.accept_15_13_3_1_1_3740 43 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 241 (accept_3_3 41 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 183 241 (accept_3_3 38 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 183 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 183 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 241 (accept_3_3 35 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 183 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 241 (accept_3_3 32 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 241 (accept_3_3 29 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 241
  (Polychromatic418967fa.accept_17_10_13_3_1_1425 27 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 241 (accept_3_3 26 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 183 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 183 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 241 (accept_3_3 23 183 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 241 (accept_3_3 20 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 241 (accept_3_3 17 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 241 (accept_3_3 14 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 241 (accept_3_3 11 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 241 (accept_3_3 8 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 241 (Polychromatic418967fa.accept_21_7_15_10_1_1368 7 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 241 (accept_3_3 5 183 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 241
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 241 (accept_3_3 2 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 183 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 182 241
  (Eq.refl Bool.true) (allA_of_3_1 60 182 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 181 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 181 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 181 241 (accept_3_3 59 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 181 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 181 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 181 241 (accept_3_3 56 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 181 241 (Polychromatic418967fa.accept_23_9_20_11_1_4501 55 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 181 241 (Polychromatic418967fa.accept_16_6_5_1_1_7761 54 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 241 (accept_3_3 53 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 181 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 181 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 181 241 (accept_3_3 50 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 181 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 181 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 241 (accept_3_3 47 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 181 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 241
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 241 (accept_3_3 44 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 241 (accept_3_3 41 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 241 (accept_3_3 38 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 241 (accept_3_3 35 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 241 (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 181 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 241 (accept_3_3 32 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 241 (accept_3_3 29 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 241
  (Polychromatic418967fa.accept_17_10_11_3_1_3442 27 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 181 241 (accept_3_3 26 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 181 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 181 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 241 (accept_3_3 23 181 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 241 (Polychromatic418967fa.accept_9_4_1_7_1_293
  22 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 241 (accept_3_3 20 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 241 (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 241 (accept_3_3 17 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 241 (accept_3_3 14 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 241 (accept_3_3 11 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 181 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 241 (accept_3_3 8 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 241 (Polychromatic418967fa.accept_21_7_13_10_1_8604 7 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 241 (accept_3_3 5 181 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 241 (accept_3_3 2 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 241 (Polychromatic418967fa.accept_19_1_10_13_1_4880 1 181 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 180 241
  (Eq.refl Bool.true) (allA_succ_of_accept 61 180 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 180 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 60 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 180 241 (accept_3_3 59 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 180 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 180 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 180 241 (accept_3_3 56 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 180 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 180 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 180 241
  (Polychromatic418967fa.accept_23_8_19_11_1_6256 54 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 180 241 (accept_3_3 53 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 180 241 (Polychromatic418967fa.accept_22_8_4_21_1_6561 52 180 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 180 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 180 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 180 241 (accept_3_3 50 180 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 180 241 (Polychromatic418967fa.accept_11_5_4_10_1_524
  49 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 180 241
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 180 241 (accept_3_3 47 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 180 241 (Polychromatic418967fa.accept_16_14_4_1_1_3049 46 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 180 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 180 241 (accept_3_3 44 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 241
  (Polychromatic418967fa.accept_13_3_11_7_1_2488 42 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 180 241 (accept_3_3 41 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 180 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 180 241 (Polychromatic418967fa.accept_22_17_4_21_1_14535 39 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 180 241 (accept_3_3 38 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 180 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 180 241 (accept_3_3 35 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 180 241 (Polychromatic418967fa.accept_19_15_9_13_1_4838 34 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 180 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 241 (accept_3_3 32 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 180
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 180 241 (accept_3_3 29 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 180 241 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 180 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 27 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 241 (accept_3_3 26 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 180
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 241
  (Polychromatic418967fa.accept_16_8_4_1_1_2102 24 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 180 241 (accept_3_3 23 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 180 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 180 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 241 (accept_3_3 20 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 180 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 241
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 241 (accept_3_3 17 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 180 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 180 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 241 (accept_3_3 14 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 180 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 241
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 180 241 (accept_3_3 11 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 180 241 (Polychromatic418967fa.accept_19_10_9_13_1_7804 10 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 9
  180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 241 (accept_3_3 8 180
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 241
  (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 180 241 (Polychromatic418967fa.accept_19_6_9_13_1_14534 6 180 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 241 (accept_3_3 5 180 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 180 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 180 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488
  3 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 241 (accept_3_3 2
  180 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 179 241 (Eq.refl
  Bool.true) (allA_of_3_1 63 179 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 178 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 178 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 178 241 (accept_3_3 62 178 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 178 241 (Polychromatic418967fa.accept_19_4_7_13_1_3480 61 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 178 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 60 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 178 241 (accept_3_3 59 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 178 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 58 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 178 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 178 241 (accept_3_3 56 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 178 241
  (Polychromatic418967fa.accept_13_2_9_7_1_164 54 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 178 241 (accept_3_3 53 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 178 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 178 241 (accept_3_3 50 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 178 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 178 241
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 48 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 178 241 (accept_3_3 47 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 178 241 (Polychromatic418967fa.accept_17_12_8_3_1_4646 46 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 178 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 178 241 (accept_3_3 44 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 178 241
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 178 241 (accept_3_3 41 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 178 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 178 241 (accept_3_3 38 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 178 241 (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 178 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 178 241
  (Polychromatic418967fa.accept_19_17_7_13_1_4833 36 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 178 241 (accept_3_3 35 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 178 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 178 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 178 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 178 241 (accept_3_3 32 178 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 178 241
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 178 241 (accept_3_3 29 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 178 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 241 (accept_3_3 26 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 178 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 178 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 241
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 178 241 (accept_3_3 23 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 178 241 (Polychromatic418967fa.accept_16_6_2_1_1_4081 22 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 178 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 241 (accept_3_3 20 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 241
  (Polychromatic418967fa.accept_15_3_13_1_1_479 18 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 241 (accept_3_3 17 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 241 (accept_3_3 14 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 241
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 241 (accept_3_3 11 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 241 (accept_3_3 8 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 241
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 241 (accept_3_3 5 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 178 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 241 (accept_3_3 2 178 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 241 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 178 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 177 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 177 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 177
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 241 (accept_3_3 62 177
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 177 241 (Polychromatic418967fa.accept_21_18_9_10_1_2571 60 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 177 241 (accept_3_3 59 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 177 241 (accept_3_3 56 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 177 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 177 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 241 (accept_3_3 53 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 177 241 (accept_3_3 50 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 177 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 177 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 241 (accept_3_3 47 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 241
  (Polychromatic418967fa.accept_19_7_6_13_1_6322 45 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 177 241 (accept_3_3 44 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 177 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 177 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 241 (accept_3_3 41 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 177 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 177 241 (accept_3_3 38 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 177 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 177 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 241 (accept_3_3 35 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 177 241 (accept_3_3 32 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 177 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 177 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 241 (accept_3_3 29 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 177 241 (accept_3_3 26 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 177 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 241 (accept_3_3 23 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 177 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 241 (accept_3_3 20 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 241 (Polychromatic418967fa.accept_20_18_17_1_1_10388 18 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 241 (accept_3_3 17 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 241 (accept_3_3 14 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 241 (accept_3_3 11 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 241
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 241 (accept_3_3 8 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 241 (Polychromatic418967fa.accept_19_7_6_13_1_6322 7 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 241 (accept_3_3 5 177 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 241 (accept_3_3 2 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 176 241
  (Eq.refl Bool.true) (allA_of_3_1 66 176 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 175 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 175 241 (accept_3_3 65 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 175 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 175 241
  (Polychromatic418967fa.accept_19_6_4_13_1_2329 63 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 175 241 (accept_3_3 62 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 175 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 175 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 175 241 (accept_3_3 59 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 241 (accept_3_3 56 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 175 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 241 (accept_3_3 53 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 241 (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 175 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 241 (accept_3_3 50 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 241 (accept_3_3 47 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 241
  (Polychromatic418967fa.accept_19_7_4_13_1_6319 45 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 241 (accept_3_3 44 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 241 (accept_3_3 41 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 241 (accept_3_3 38 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 241 (accept_3_3 35 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 175 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 241 (accept_3_3 32 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 241 (Polychromatic418967fa.accept_27_4_13_25_1_14533 31 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 241 (accept_3_3 29 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 175 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 241
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 241 (accept_3_3 26 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 241 (accept_3_3 23 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 241 (accept_3_3 20 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 241 (accept_3_3 17 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 241 (accept_3_3 14 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 241 (accept_3_3 11 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 241 (accept_3_3 8 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 241 (accept_3_3 5 175 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 175 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 241 (accept_3_3 2 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 175 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 174
  241 (Eq.refl Bool.true) (allA_succ_of_accept 67 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 174 241
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 174 241 (accept_3_3 65 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 174 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 174 241 (accept_3_3 62 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 174 241 (Polychromatic418967fa.accept_16_13_14_1_1_2094 61 174 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 174 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 174 241 (accept_3_3 59 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 174 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 174 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 174 241 (accept_3_3 56 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 174 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 174 241
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 174 241 (accept_3_3 53 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 174 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 174 241 (accept_3_3 50 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 174 241
  (Polychromatic418967fa.accept_19_10_3_13_1_6284 48 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 174 241 (accept_3_3 47 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 174 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 174 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 174 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 174
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 174 241 (accept_3_3 44 174
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 174 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 174 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 174 241 (accept_3_3 41 174 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 174 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 241 (accept_3_3 38
  174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 174 241 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 174 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 241 (accept_3_3 35 174 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 174 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 34 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 174 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 174 241 (accept_3_3 32 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 174 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 241 (accept_3_3 29 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 174 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 174 241 (accept_3_3 26 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 174 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 174 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 241 (accept_3_3 23 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 241
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 174 241 (accept_3_3 20 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 174 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 241 (accept_3_3 17 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 174 241 (accept_3_3 14 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 174 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 174 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 241 (accept_3_3 11 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 174 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 174 241 (accept_3_3 8 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  174 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 174 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 241 (accept_3_3 5 174 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 174 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 174 241 (accept_3_3 2 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  174 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 174 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 173
  241 (Eq.refl Bool.true) (allA_of_3_1 69 173 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 172 241
  (Eq.refl Bool.true) (allA_succ_of_accept 69 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 172 241 (accept_3_3 68 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 172 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 172 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 172 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 172 241 (accept_3_3 65 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 172 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 172 241 (accept_3_3 62 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 172 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 172 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 172 241 (accept_3_3 59 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 172 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 172 241 (accept_3_3 56 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 172 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 172 241
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 172 241 (accept_3_3 53 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 172 241 (Polychromatic418967fa.accept_16_4_12_1_1_1204 52 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 172 241 (accept_3_3 50 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 172 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 172 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 172 241 (accept_3_3 47 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 172 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 172 241 (accept_3_3 44 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 172 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 172 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 172 241 (accept_3_3 41 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 172 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 172 241 (accept_3_3 38 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 172 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 172 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 172 241 (accept_3_3 35 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 172 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 172 241 (accept_3_3 32 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 172 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 172 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 172 241 (accept_3_3 29 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 172 241 (Polychromatic418967fa.accept_17_11_2_3_1_8468 28 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 172 241 (accept_3_3 26 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 172 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 172 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 172 241 (accept_3_3 23 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 172 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 241 (accept_3_3 20 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 172 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 241
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 172 241 (accept_3_3 17 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 172 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 241 (accept_3_3 14 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 172 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 172 241 (accept_3_3 11 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 172 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 241 (accept_3_3 8 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 172 241 (Polychromatic418967fa.accept_14_7_4_3_1_488 7 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 172 241 (accept_3_3 5 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  172 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 172 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 172 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 241 (accept_3_3 2 172 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 172 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 171 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 69 171
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 241 (accept_3_3 68 171
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 241
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 241 (accept_3_3 65 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 171 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834
  63 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 241 (accept_3_3 62
  171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 241
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 61 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 171 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 60 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 241 (accept_3_3 59 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 241 (Polychromatic418967fa.accept_12_9_3_1_1_303
  57 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 241 (accept_3_3 56
  171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 241
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 241 (accept_3_3 53 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 171 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 241
  (Polychromatic418967fa.accept_21_9_3_10_1_8573 51 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 171 241 (accept_3_3 50 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 171 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 171 241 (Polychromatic418967fa.accept_13_9_2_7_1_1083 48 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 241 (accept_3_3 47 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 171 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 171 241 (accept_3_3 44 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 171 241 (Polychromatic418967fa.accept_17_9_1_3_1_4626 43 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 241 (accept_3_3 41 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 241
  (Polychromatic418967fa.accept_15_9_6_1_1_493 39 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 171 241 (accept_3_3 38 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 171 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 171 241 (Polychromatic418967fa.accept_17_2_1_3_1_2357 36 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 241 (accept_3_3 35 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 171 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 241 (accept_3_3 32 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 31 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 241 (accept_3_3 29 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 241
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 171 241 (accept_3_3 26 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 171 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 171 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 241 (accept_3_3 23 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 241 (accept_3_3 20 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 241 (Polychromatic418967fa.accept_17_2_1_3_1_2357 19 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 241 (accept_3_3 17 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 241
  (Polychromatic418967fa.accept_16_15_11_1_1_7767 15 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 241 (accept_3_3 14 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 241 (Polychromatic418967fa.accept_21_13_3_10_1_2592 13 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 241
  (Polychromatic418967fa.accept_16_12_11_1_1_4088 12 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 241 (accept_3_3 11 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 241 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 171 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 241 (accept_3_3 8 171 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091
  7 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 241 (accept_3_3 5 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 241 (accept_3_3 2 171 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 241 (Polychromatic418967fa.accept_21_1_3_10_1_5401 1 171 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 170 241 (Eq.refl Bool.true)
  (allA_of_3_1 72 170 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 169 241 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 169 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 169 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 169 241 (accept_3_3 71 169 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 169 241 (Polychromatic418967fa.accept_20_10_9_1_1_3076 70 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 169 241
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 69 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 169 241 (accept_3_3 68 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 169 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 169 241 (Polychromatic418967fa.accept_16_2_9_1_1_6404 66 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 241 (accept_3_3 65 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 241 (Polychromatic418967fa.accept_17_13_16_3_1_1431 64 169
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 241
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 241 (accept_3_3 62 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 241 (accept_3_3 59 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 241
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 57 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 241 (accept_3_3 56 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 55 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 241 (accept_3_3 53 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 241 (accept_3_3 50 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 241 (Polychromatic418967fa.accept_11_5_4_10_1_524 49 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 241 (accept_3_3 47 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 169 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 241 (accept_3_3 44 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 241 (Polychromatic418967fa.accept_23_20_8_11_1_11355 43 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 241 (accept_3_3 41 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 169 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 241 (accept_3_3 38 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 241 (Polychromatic418967fa.accept_21_15_1_10_1_8592 36 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 241 (accept_3_3 35 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 241 (Polychromatic418967fa.accept_16_2_9_1_1_6404 34 169
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 241 (accept_3_3 32 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 241 (Polychromatic418967fa.accept_25_6_19_16_1_12800 31 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 241 (accept_3_3 29 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 241 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 169
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 241 (accept_3_3 26 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 241 (Polychromatic418967fa.accept_16_8_9_1_1_7753 24 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 241 (accept_3_3 23 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 22 169
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 241
  (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 241 (accept_3_3 20 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 241 (accept_3_3 17 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 241 (accept_3_3 14 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 241 (Polychromatic418967fa.accept_16_13_9_1_1_3022 13 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 241 (accept_3_3 11 169 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 241 (Polychromatic418967fa.accept_16_10_9_1_1_9973 10 169 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 241 (accept_3_3 8 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 241 (Polychromatic418967fa.accept_17_7_16_3_1_4660 7 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 241 (Polychromatic418967fa.accept_19_6_17_13_1_2323 6 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 241 (accept_3_3 5 169 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 241
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 3 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 241 (accept_3_3 2 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 241 (Polychromatic418967fa.accept_25_1_19_16_1_12799 1 169 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  168 241 (Eq.refl Bool.true) (allA_succ_of_accept 73 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 168 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 168 241
  (Polychromatic418967fa.accept_19_15_16_13_1_1336 72 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 168 241 (accept_3_3 71 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 168 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 70 168 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 168 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 69 168
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 168 241 (accept_3_3 68 168
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 168 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 168 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 168 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 168 241 (accept_3_3 65 168 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 168 241 (Polychromatic418967fa.accept_10_3_8_1_1_182
  63 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 168 241 (accept_3_3 62
  168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 168 241
  (Polychromatic418967fa.accept_25_11_18_16_1_14532 61 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 168 241 (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 168 241 (accept_3_3 59 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 168 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 168 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 168 241 (accept_3_3 56 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 168 241 (Polychromatic418967fa.accept_22_10_14_21_1_8328 54 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 168 241 (accept_3_3 53 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 52 168
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 168 241
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 168 241 (accept_3_3 50 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 168 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 168 241 (accept_3_3 47 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 241
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 168 241 (accept_3_3 44 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 168 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 168 241 (Polychromatic418967fa.accept_23_19_7_11_1_6231 42 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 168 241 (accept_3_3 41 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 168 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 168 241 (accept_3_3 38 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 168 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 241 (accept_3_3 35 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 241 (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 168
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 168 241
  (Polychromatic418967fa.accept_10_3_8_1_1_182 33 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 168 241 (accept_3_3 32 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 168 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 241 (accept_3_3 29 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 168 241
  (Polychromatic418967fa.accept_18_9_6_7_1_6719 27 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 168 241 (accept_3_3 26 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 168 241 (Polychromatic418967fa.accept_16_9_8_1_1_1228 25 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 168 241 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 241 (accept_3_3 23 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 168 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 168 241 (accept_3_3 20 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 168 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 241 (accept_3_3 17 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 241 (Polychromatic418967fa.accept_23_16_7_11_1_14531 16
  168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 241
  (Polychromatic418967fa.accept_16_15_8_1_1_9959 15 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 168 241 (accept_3_3 14 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 168 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 241 (accept_3_3 11 168 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 241
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 168 241 (accept_3_3 8 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  168 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 168 241 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 241 (accept_3_3 5 168 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 168 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 241 (accept_3_3 2 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75
  167 241 (Eq.refl Bool.true) (allA_of_3_1 75 167 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 166 241
  (Eq.refl Bool.true) (allA_succ_of_accept 75 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 166 241 (accept_3_3 74 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 166 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 166 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 166 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 166 241 (accept_3_3 71 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 166 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 70 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 166 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 166 241 (accept_3_3 68 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 166 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 166 241 (accept_3_3 65 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 166 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 166 241 (accept_3_3 62 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 166 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 61 166 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 166 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 166 241 (accept_3_3 59 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 166 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 166 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 166 241 (accept_3_3 56 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 166 241
  (Polychromatic418967fa.accept_19_16_14_13_1_2313 54 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 166 241 (accept_3_3 53 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 166 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 166 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 166 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 166 241 (accept_3_3 50 166 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 166 241
  (Polychromatic418967fa.accept_18_13_4_7_1_4086 49 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 166 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 166 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 166 241 (accept_3_3 47 166 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 166 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 166 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45
  166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 241 (accept_3_3 44
  166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 166 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 166 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 166 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 166 241 (accept_3_3 41 166 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 166 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 166 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 166 241 (accept_3_3 38 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 166 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 166 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 241 (accept_3_3 35 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 166 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 166 241 (accept_3_3 32 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 166 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 166 241 (accept_3_3 29 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 241 (accept_3_3 26 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 166 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 241 (accept_3_3 23 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 241 (accept_3_3 20 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 241 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 241 (accept_3_3 17 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 166 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 241 (accept_3_3 14 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 241 (accept_3_3 11 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 241 (accept_3_3 8 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 241 (accept_3_3 5 166 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 166 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 241 (accept_3_3 2 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 166 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 165 241 (Eq.refl Bool.true) (allA_succ_of_accept 76 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 165 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 165 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 165 241 (accept_3_3 74 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 165 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 165 241 (Polychromatic418967fa.accept_21_9_18_10_1_5388 72 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 241 (accept_3_3 71 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 165 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 165 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 165 241 (accept_3_3 68 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 165 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 165 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 66 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 241 (accept_3_3 65 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 165 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 165 241 (accept_3_3 62 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 165 241 (Polychromatic418967fa.accept_16_13_5_1_1_3017 61 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 165 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 241 (accept_3_3 59 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 165 241 (accept_3_3 56 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 165 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 165 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 241 (accept_3_3 53 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 165 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 165 241 (accept_3_3 50 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 165 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 165 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 241 (accept_3_3 47 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 241
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 165 241 (accept_3_3 44 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 165 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 165 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 241 (accept_3_3 41 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 241 (accept_3_3 38 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 165 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 241 (accept_3_3 35 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 241 (accept_3_3 32 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 241 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 241 (accept_3_3 29 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 241 (accept_3_3 26 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 165 241 (Polychromatic418967fa.accept_16_9_5_1_1_1259 25 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 165 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 241 (accept_3_3 23 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 241 (accept_3_3 20 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 241 (Polychromatic418967fa.accept_22_18_11_21_1_14530 18 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 241 (accept_3_3 17 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 241 (accept_3_3 14 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 241 (accept_3_3 11 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 241 (accept_3_3 8 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 241 (accept_3_3 5 165 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 241 (accept_3_3 2 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 164 241 (Eq.refl Bool.true) (allA_of_3_1 78 164 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 163 241
  (Eq.refl Bool.true) (allA_succ_of_accept 78 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 163 241 (accept_3_3 77 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 163 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 163 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 163 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 163 241 (accept_3_3 74 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 163 241 (Polychromatic418967fa.accept_19_16_11_13_1_4944 73 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 163 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 241 (accept_3_3 71 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 163 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 241 (accept_3_3 68 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 241 (accept_3_3 65 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 241
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 241 (accept_3_3 62 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 241 (accept_3_3 59 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 241 (accept_3_3 56 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 241 (accept_3_3 53 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 52 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 241 (accept_3_3 50 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 241 (accept_3_3 47 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 241 (accept_3_3 44 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 241 (accept_3_3 41 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 241 (accept_3_3 38 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 241 (Polychromatic418967fa.accept_23_14_2_11_1_11351 37 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 241 (accept_3_3 35 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 163 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 241 (accept_3_3 32 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 241 (accept_3_3 29 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 241 (accept_3_3 26 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 241 (accept_3_3 23 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 241 (accept_3_3 20 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 241 (accept_3_3 17 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 241 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 163 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 241 (accept_3_3 14 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 241 (accept_3_3 11 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 241
  (Polychromatic418967fa.accept_17_9_10_3_1_3423 9 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 241 (accept_3_3 8 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 241 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 241 (accept_3_3 5 163 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 241 (accept_3_3 2 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 162 241 (Eq.refl Bool.true) (allA_succ_of_accept 79 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50
  79 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 162 241
  (Polychromatic418967fa.accept_17_10_9_3_1_7144 78 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 162 241 (accept_3_3 77 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 162 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 76 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 162 241 (accept_3_3 74 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 162 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 162 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 162 241 (accept_3_3 71 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 162 241 (Polychromatic418967fa.accept_16_6_2_1_1_4081 70 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 162 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 162 241 (accept_3_3 68 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 162 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 162 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 162 241 (accept_3_3 65 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 162 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 64 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 162 241 (accept_3_3 62 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 162 241 (accept_3_3 59 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 162 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 162 241 (Polychromatic418967fa.accept_16_9_2_1_1_3077 57 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 241 (accept_3_3 56 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 162 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 162 241 (accept_3_3 53 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 162 241 (Polychromatic418967fa.accept_17_1_9_3_1_7161 52 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 241 (accept_3_3 50 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 241
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 241 (accept_3_3 47 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 162 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 241 (Polychromatic418967fa.accept_17_11_9_3_1_1463 45 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 241 (accept_3_3 44 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 162 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 241
  (Polychromatic418967fa.accept_11_9_8_10_1_934 42 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 162 241 (accept_3_3 41 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 162 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 241 (accept_3_3 38 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 162 241 (accept_3_3 35 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 162 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 162 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 241 (accept_3_3 32 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 162 241 (accept_3_3 29 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 162 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 241 (accept_3_3 26 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 241
  (Polychromatic418967fa.accept_19_5_10_13_1_4883 24 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 162 241 (accept_3_3 23 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 22 162 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 241 (Polychromatic418967fa.accept_19_2_10_13_1_9147 21 162
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 241 (accept_3_3 20 162
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 162 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 162 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 241 (accept_3_3 17 162 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 162 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 241 (accept_3_3 14
  162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 241
  (Polychromatic418967fa.accept_10_3_2_1_1_839 13 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 162 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 162 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 241 (accept_3_3 11 162 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 162 241 (Polychromatic418967fa.accept_17_10_9_3_1_7144 10 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 162 241 (accept_3_3 8 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  162 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 162 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 241 (accept_3_3 5 162 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 162 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 162 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 162 241 (accept_3_3 2 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  162 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 162 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 162 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 161 241 (Eq.refl Bool.true) (allA_of_3_1 81 161 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 82 160 241 (Eq.refl Bool.true) (allA_succ_of_accept 81 160 241 (Polychromatic418967fa.accept_6_3_4_1_1_8
  81 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 160 241 (accept_3_3 80
  160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 160 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 160 241 (Polychromatic418967fa.accept_17_10_7_3_1_727 78 160 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 160 241 (accept_3_3 77 160 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 160 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 76 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 160 241 (accept_3_3 74 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 160 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 160 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 160 241 (accept_3_3 71 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 160 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 160 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 160 241 (accept_3_3 68 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 160 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 160 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 66 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 160 241 (accept_3_3 65 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 160 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 160 241 (accept_3_3 62 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 160 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 160 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 160 241 (accept_3_3 59 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 160 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 160 241 (accept_3_3 56 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 160 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 160 241 (Polychromatic418967fa.accept_15_9_10_1_1_1062 54 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 241 (accept_3_3 53 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 160 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 160 241 (accept_3_3 50 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 160 241 (Polychromatic418967fa.accept_11_5_6_10_1_1432 49 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 160 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 241 (accept_3_3 47 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 160 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 160 241 (accept_3_3 44 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 160 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 160 241 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 241 (accept_3_3 41 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 160 241 (Polychromatic418967fa.accept_18_4_16_7_1_1873 40 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 160 241 (accept_3_3 38 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 160 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 160 241 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 160 241 (accept_3_3 35 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 160 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 160 241 (accept_3_3 32 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 160 241 (Polychromatic418967fa.accept_23_8_22_11_1_14529 31 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 160 241 (accept_3_3 29 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 160 241 (accept_3_3 26 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 160 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 160 241 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 241 (accept_3_3 23 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 160 241 (accept_3_3 20 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 160 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 160 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 241 (accept_3_3 17 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 160 241 (accept_3_3 14 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 160 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 241 (accept_3_3 11 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 160
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 241 (accept_3_3 8 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 241 (Polychromatic418967fa.accept_13_6_4_7_1_2464 6 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 241 (accept_3_3 5 160 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 160 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 241 (accept_3_3 2 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 241 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 160 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 159 241 (Eq.refl Bool.true) (allA_succ_of_accept 82 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2
  82 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 159 241
  (Polychromatic418967fa.accept_11_4_5_10_1_926 81 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 159 241 (accept_3_3 80 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 159 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 159 241 (accept_3_3 77 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 159 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 159 241 (accept_3_3 74 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 159 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 159 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 159 241 (accept_3_3 71 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 159 241 (accept_3_3 68 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 159 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 241 (accept_3_3 65 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 241
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 159 241 (accept_3_3 62 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 159 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 159 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 60 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 241 (accept_3_3 59 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 159 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 159 241 (accept_3_3 56 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 159 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 241 (accept_3_3 53 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 159 241 (accept_3_3 50 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 159 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 159 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 241 (accept_3_3 47 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 159 241 (accept_3_3 44 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 159 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 241 (accept_3_3 41 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 159 241 (accept_3_3 38 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 159 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 159 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 241 (accept_3_3 35 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 159 241 (accept_3_3 32 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 159 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 241 (accept_3_3 29 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 241
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 241 (accept_3_3 26 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 241 (Polychromatic418967fa.accept_13_11_3_7_1_2513 24 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 241 (accept_3_3 23 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 241 (accept_3_3 20 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 241 (accept_3_3 17 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 241 (accept_3_3 14 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 241 (accept_3_3 11 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 241 (accept_3_3 8 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 241 (accept_3_3 5 159 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 241 (accept_3_3 2 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 158 241 (Eq.refl Bool.true) (allA_of_3_1 84 158 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 157 241 (Eq.refl Bool.true) (allA_succ_of_accept 84 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299
  84 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 157 241 (accept_3_3 83
  157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 157 241
  (Polychromatic418967fa.accept_9_1_4_7_1_7 82 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 157 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 157 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 157 241 (accept_3_3 80 157 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 157 241 (Polychromatic418967fa.accept_24_7_13_1_1_9522 79 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 157 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 157 241 (accept_3_3 77 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 76 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 157 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 241 (accept_3_3 74 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 241
  (Polychromatic418967fa.accept_22_6_3_21_1_14528 72 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 157 241 (accept_3_3 71 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 157 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 157 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 241 (accept_3_3 68 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 241
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 67 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 157 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 157 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 241 (accept_3_3 65 157 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 241
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 241 (accept_3_3 62 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 241 (Polychromatic418967fa.accept_23_15_19_11_1_14527 61 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 241 (accept_3_3 59 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 58 157
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 241 (accept_3_3 56 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 241 (accept_3_3 53 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 241 (accept_3_3 50 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 241 (Polychromatic418967fa.accept_19_11_5_13_1_11849 49 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 241 (accept_3_3 47 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 241
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 241 (accept_3_3 44 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 241 (Polychromatic418967fa.accept_24_19_13_1_1_9452 43 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 241 (accept_3_3 41 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 241 (accept_3_3 38 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 241 (accept_3_3 35 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 34 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 241 (accept_3_3 32 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 241 (Polychromatic418967fa.accept_19_12_5_13_1_14492 31 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 241 (accept_3_3 29 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 241
  (Polychromatic418967fa.accept_19_8_5_13_1_7800 27 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 241 (accept_3_3 26 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 241 (accept_3_3 23 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 241 (Polychromatic418967fa.accept_18_4_13_7_1_5395 22 157 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 241 (accept_3_3 20 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 241 (accept_3_3 17 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 157
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 241 (accept_3_3 14 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 241 (Polychromatic418967fa.accept_17_13_4_3_1_1446 13 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 241 (accept_3_3 11 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 241
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 241 (accept_3_3 8 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 241 (accept_3_3 5 157 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 157 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 241 (accept_3_3 2 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 157 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 86 156 241 (Eq.refl Bool.true) (allA_succ_of_accept 85 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257
  85 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 156 241
  (Polychromatic418967fa.accept_15_9_6_1_1_493 84 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 156 241 (accept_3_3 83 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 156 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 156 241 (Polychromatic418967fa.accept_21_18_9_10_1_2571 81 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 156 241 (accept_3_3 80 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 156 241 (Polychromatic418967fa.accept_19_3_4_13_1_4864 79 156
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 156 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 156 241 (accept_3_3 77 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 156 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 156 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 156 241 (accept_3_3 74 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 156 241
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 156 241 (accept_3_3 71 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 156 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 156 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 156 241 (accept_3_3 68 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 156 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 156 241
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 66 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 156 241 (accept_3_3 65 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 156 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 241 (accept_3_3 62 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 156 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 156 241 (accept_3_3 59 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 156 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 241 (accept_3_3 56 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 156 241 (accept_3_3 53 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 156 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 156 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 241 (accept_3_3 50 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 241 (accept_3_3 47 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 156 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 241 (accept_3_3 44 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 241 (accept_3_3 41 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 241 (accept_3_3 38 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 156 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 241 (accept_3_3 35 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 241 (accept_3_3 32 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 241
  (Polychromatic418967fa.accept_22_8_2_21_1_9874 30 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 156 241 (accept_3_3 29 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 156 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 156 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 241 (accept_3_3 26 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 241 (accept_3_3 23 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 241 (accept_3_3 20 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 241 (accept_3_3 17 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 241 (Polychromatic418967fa.accept_21_16_9_10_1_14488 16 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 241 (accept_3_3 14 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 241 (accept_3_3 11 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 241 (accept_3_3 8 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 241 (accept_3_3 5 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 156 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 241 (accept_3_3 2 156 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 155 241
  (Eq.refl Bool.true) (allA_of_3_1 87 155 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 154 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 154 241 (accept_3_3 86 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 154 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 154 241 (accept_3_3 83 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 154 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 82 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 154 241 (accept_3_3 80 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 154 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 154 241 (accept_3_3 77 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 154 241 (accept_3_3 74 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 154 241 (Polychromatic418967fa.accept_16_9_10_1_1_2998 73 154 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 154 241
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 72 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 154 241 (accept_3_3 71 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 154 241 (Polychromatic418967fa.accept_13_5_11_7_1_559 70 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 241 (accept_3_3 68 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 154 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 154 241 (accept_3_3 65 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 154 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 154 241 (accept_3_3 62 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 154 241 (Polychromatic418967fa.accept_13_9_11_7_1_1077 61 154 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 154 241 (accept_3_3 59 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 154 241 (accept_3_3 56 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 241
  (Polychromatic418967fa.accept_19_16_2_13_1_13234 54 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 154 241 (accept_3_3 53 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 154 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 154 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 154 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 241 (accept_3_3 50 154 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293
  49 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 154 241 (accept_3_3 47 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 154 241 (Polychromatic418967fa.accept_19_8_2_13_1_2328 46 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 241 (accept_3_3 44 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 154 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 154 241 (accept_3_3 41 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 241 (accept_3_3 38 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 154 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 241
  (Polychromatic418967fa.accept_17_2_1_3_1_2357 36 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 154 241 (accept_3_3 35 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 154 241 (Polychromatic418967fa.accept_19_15_2_13_1_10598 34 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 241 (accept_3_3 32 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 154 241 (accept_3_3 29 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 154 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 241 (accept_3_3 26 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 241 (accept_3_3 23 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 241 (accept_3_3 20 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 241
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 241 (accept_3_3 17 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 241 (accept_3_3 14 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 241 (accept_3_3 11 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 241 (Polychromatic418967fa.accept_19_10_2_13_1_9183 10 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 154 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 241 (accept_3_3 8 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 241 (accept_3_3 5 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 154 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 241 (accept_3_3 2 154 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 241 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 154 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 153 241
  (Eq.refl Bool.true) (allA_succ_of_accept 88 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 153 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 87 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 153 241 (accept_3_3 86 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 153 241 (Polychromatic418967fa.accept_16_5_9_1_1_2070 85 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 153 241 (Polychromatic418967fa.accept_19_8_1_13_1_10590 84 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 153 241 (accept_3_3 83 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 153 241 (accept_3_3 80 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 153 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 153 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 153 241 (accept_3_3 77 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 153 241 (accept_3_3 74 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 153 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 153 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 241 (accept_3_3 71 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 241
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 69 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 241 (accept_3_3 68 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 153 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 153 241 (Polychromatic418967fa.accept_14_10_13_3_1_2552 66 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 241 (accept_3_3 65 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 241 (accept_3_3 62 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 241 (Polychromatic418967fa.accept_16_13_9_1_1_3022 61 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 241 (accept_3_3 59 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 241
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 57 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 241 (accept_3_3 56 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 241 (Polychromatic418967fa.accept_19_16_1_13_1_4860 54 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 241 (accept_3_3 53 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 241 (accept_3_3 50 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 153 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 49 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 241 (accept_3_3 47 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 241
  (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 241 (accept_3_3 44 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 153 241 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 241 (accept_3_3 41 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 241 (accept_3_3 38 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 241 (accept_3_3 35 153 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 153 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 241
  (Polychromatic418967fa.accept_19_14_1_13_1_7810 33 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 241 (accept_3_3 32 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 241 (Polychromatic418967fa.accept_19_12_1_13_1_11823 31 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 241 (Polychromatic418967fa.accept_7_2_6_3_1_100
  30 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 241 (accept_3_3 29
  153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 241
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 153 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 241 (accept_3_3 26 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 153 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 241
  (Polychromatic418967fa.accept_14_10_13_3_1_2552 24 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 241 (accept_3_3 23 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 153
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 241 (accept_3_3 20 153
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 241
  (Polychromatic418967fa.accept_15_4_3_1_1_487 19 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 153 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 241 (accept_3_3 17 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 241 (Polychromatic418967fa.accept_12_3_9_1_1_290
  15 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 241 (accept_3_3 14
  153 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 241
  (Polychromatic418967fa.accept_15_13_3_1_1_3740 13 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 153 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 241 (accept_3_3 11 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 241 (accept_3_3 8 153
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 241
  (Polychromatic418967fa.accept_19_7_1_13_1_4861 7 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 153 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 6 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 241 (accept_3_3 5 153 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 153 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 241 (accept_3_3 2 153
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 241
  (Polychromatic418967fa.accept_27_1_18_25_1_6791 1 153 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153 241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  90 152 241 (Eq.refl Bool.true) (allA_of_3_1 90 152 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 151 241
  (Eq.refl Bool.true) (allA_succ_of_accept 90 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 151 241 (accept_3_3 89 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 151 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 88 151
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 151 241
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 87 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 151 241 (accept_3_3 86 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 151 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 151 241 (Polychromatic418967fa.accept_19_8_18_13_1_11803 84 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 241 (accept_3_3 83 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 241
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 151 241 (accept_3_3 80 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 151 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 79 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 241 (accept_3_3 77 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 241
  (Polychromatic418967fa.accept_11_9_8_10_1_934 75 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 241 (accept_3_3 74 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 241 (Polychromatic418967fa.accept_19_16_18_13_1_4855 73 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 241 (Polychromatic418967fa.accept_16_8_7_1_1_8875 72 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 241 (accept_3_3 71 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 241 (accept_3_3 68 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 241 (Polychromatic418967fa.accept_13_2_8_7_1_2424 67 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 241 (accept_3_3 65 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 241
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 241 (accept_3_3 62 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 241 (Polychromatic418967fa.accept_22_16_19_21_1_14526 60 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 241 (accept_3_3 59 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 241 (accept_3_3 56 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 241 (accept_3_3 53 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 241 (Polychromatic418967fa.accept_17_1_15_3_1_1501 52 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 241
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 241 (accept_3_3 50 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 241 (accept_3_3 47 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 241
  (Polychromatic418967fa.accept_27_18_16_25_1_14525 45 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 151 241 (accept_3_3 44 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 151 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 241 (accept_3_3 41 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088
  40 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 241
  (Polychromatic418967fa.accept_19_1_18_13_1_7796 39 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 151 241 (accept_3_3 38 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 151 241 (Polychromatic418967fa.accept_20_17_11_1_1_8865 37 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 241 (accept_3_3 35
  151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 151 241 (Polychromatic418967fa.accept_19_14_18_13_1_7823 33 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 241 (accept_3_3 32 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 31 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 241 (accept_3_3 29 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 241 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 241 (accept_3_3 26 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 151 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 241
  (Polychromatic418967fa.accept_16_8_7_1_1_8875 24 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 241 (accept_3_3 23 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 21 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 241 (accept_3_3 20 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 241 (Polychromatic418967fa.accept_21_19_4_10_1_3914 19 151
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 241 (accept_3_3 17 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 241 (accept_3_3 14 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 241
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 241 (accept_3_3 11 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 241 (accept_3_3 8 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 241
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 241 (accept_3_3 5 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 241 (Polychromatic418967fa.accept_20_4_11_1_1_10409 4 151 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 241 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 241 (accept_3_3 2 151 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 150 241
  (Eq.refl Bool.true) (allA_succ_of_accept 91 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 150 241
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 90 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 150 241 (accept_3_3 89 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 150 241 (Polychromatic418967fa.accept_23_19_12_11_1_9742 88 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 150 241 (accept_3_3 86 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 150 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 150 241 (accept_3_3 83 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 150 241 (Polychromatic418967fa.accept_18_9_6_7_1_6719 81 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 150 241 (accept_3_3 80 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 150 241
  (Polychromatic418967fa.accept_21_15_3_10_1_8533 78 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 150 241 (accept_3_3 77 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 150 241 (accept_3_3 74 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285
  73 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 150 241
  (Polychromatic418967fa.accept_19_15_17_13_1_4901 72 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 150 241 (accept_3_3 71 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 150 241 (Polychromatic418967fa.accept_17_2_14_3_1_4679 70 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 150 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 69 150
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 241 (accept_3_3 68 150
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 150 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 67 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 150 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 150 241 (accept_3_3 65 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63
  150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 241 (accept_3_3 62
  150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 241
  (Polychromatic418967fa.accept_19_4_17_13_1_4929 61 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 150 241 (Polychromatic418967fa.accept_21_18_3_10_1_8534 60 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 150 241 (accept_3_3 59 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 150 241 (accept_3_3 56 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 150 241 (Polychromatic418967fa.accept_19_16_17_13_1_9125 54 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 150 241 (accept_3_3 53 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 241 (Polychromatic418967fa.accept_28_24_10_17_1_14524 52
  150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 150 241 (accept_3_3 50 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 150 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 241 (accept_3_3 47 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 241
  (Polychromatic418967fa.accept_17_11_14_3_1_1427 45 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 150 241 (accept_3_3 44 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 241 (Polychromatic418967fa.accept_19_4_17_13_1_4929 42 150
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 241 (accept_3_3 41 150
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 241 (accept_3_3 38 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 241 (Polychromatic418967fa.accept_11_3_7_10_1_180
  36 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 150 241 (accept_3_3 35
  150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 241
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 150 241 (Polychromatic418967fa.accept_20_13_10_1_1_5903 33 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 241 (accept_3_3 32 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 241 (accept_3_3 29 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 241 (accept_3_3 26 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 25 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 241
  (Polychromatic418967fa.accept_20_4_10_1_1_13131 24 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 241 (accept_3_3 23 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 150 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 241 (accept_3_3 20 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 241
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 241 (accept_3_3 17 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 241 (Polychromatic418967fa.accept_19_16_17_13_1_9125 16 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 241 (accept_3_3 14 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 150 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 241 (accept_3_3 11 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 241 (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 241 (accept_3_3 8 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 241
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 6 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 241 (accept_3_3 5 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 150 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 241 (accept_3_3 2 150 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 150 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 149 241
  (Eq.refl Bool.true) (allA_of_3_1 93 149 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 148 241 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 148 241 (accept_3_3 92 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 148 241
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 90 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 148 241 (accept_3_3 89 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 148 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 148 241 (accept_3_3 86 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 148 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 85 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 148 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 148 241 (accept_3_3 83 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 148 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 148 241 (accept_3_3 80 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 148 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 148 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 148 241 (accept_3_3 77 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 148 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 76 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 148 241 (accept_3_3 74 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 148 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 148 241 (accept_3_3 71 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 148 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 70 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 241 (accept_3_3 68 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 148 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 148 241 (accept_3_3 65 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 241 (accept_3_3 62 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 148 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 241 (accept_3_3 59 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 241 (accept_3_3 56 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 241 (accept_3_3 53 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 241 (Polychromatic418967fa.accept_18_16_4_7_1_2927 52 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 241 (accept_3_3 50 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 241 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 241 (accept_3_3 47 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 241 (accept_3_3 44 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 241 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 241 (accept_3_3 41 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 241 (accept_3_3 38 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 241
  (Polychromatic418967fa.accept_19_17_15_13_1_7794 36 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 148 241 (accept_3_3 35 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 148 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 148 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 241 (accept_3_3 32 148 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 241
  (Polychromatic418967fa.accept_18_13_4_7_1_4086 31 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 148 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 148 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 241 (accept_3_3 29 148 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 27
  148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 241 (accept_3_3 26
  148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 148 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 148 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 241 (accept_3_3 23 148 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 148 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 241 (accept_3_3 20 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 241 (accept_3_3 17 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 241 (accept_3_3 14 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 241 (accept_3_3 11 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 241 (accept_3_3 8 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 241 (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 241 (accept_3_3 5 148 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 148 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 241 (accept_3_3 2 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 147
  241 (Eq.refl Bool.true) (allA_succ_of_accept 94 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 147 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 93 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 147 241 (accept_3_3 92 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 147 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 241 (accept_3_3 89 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 147 241 (accept_3_3 86 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 147 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 147 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 84 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 241 (accept_3_3 83 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 147 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 147 241 (accept_3_3 80 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 147 241 (Polychromatic418967fa.accept_15_4_12_1_1_1081 79 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 241 (accept_3_3 77 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 241
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 75 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 147 241 (accept_3_3 74 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 147 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 147 241 (Polychromatic418967fa.accept_19_15_14_13_1_2343 72 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 241 (accept_3_3 71 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 147 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 241 (accept_3_3 68 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 147 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 241 (accept_3_3 65 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 241
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 63 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 147 241 (accept_3_3 62 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 147 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 61 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 147 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 241 (accept_3_3 59 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 241 (accept_3_3 56 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 241 (accept_3_3 53 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 241 (accept_3_3 50 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 241 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 241 (accept_3_3 47 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 147 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 241 (accept_3_3 44 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 241 (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 241 (accept_3_3 41 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 241
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 241 (accept_3_3 38 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 241 (accept_3_3 35 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 241 (accept_3_3 32 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 241 (accept_3_3 29 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 241
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 241 (accept_3_3 26 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 241 (accept_3_3 23 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 241 (accept_3_3 20 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 241 (accept_3_3 17 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 241 (accept_3_3 14 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 241 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 241 (accept_3_3 11 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 241 (accept_3_3 8 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 241 (Polychromatic418967fa.accept_23_7_9_11_1_14523 7 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 241 (accept_3_3 5 147 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 241
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 241 (accept_3_3 2 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 147 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 146
  241 (Eq.refl Bool.true) (allA_of_3_1 96 146 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 145 241
  (Eq.refl Bool.true) (allA_succ_of_accept 96 145 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 145 241 (accept_3_3 95 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 145 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 145 241 (accept_3_3 92 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 145 241 (Polychromatic418967fa.accept_17_6_9_3_1_704 91 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 145 241 (Polychromatic418967fa.accept_19_14_12_13_1_3485 90 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 145 241 (accept_3_3 89 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 88 145
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 241 (accept_3_3 86 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 145 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 241 (accept_3_3 83 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 145 241 (Polychromatic418967fa.accept_14_12_5_3_1_1011 82 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 241
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 145 241 (accept_3_3 80 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 145 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 241 (accept_3_3 77 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 75 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 241 (accept_3_3 74 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 241 (Polychromatic418967fa.accept_13_8_2_7_1_2452 73 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 145 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 241 (accept_3_3 71 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 70 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 241 (accept_3_3 68 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 241 (accept_3_3 65 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 241
  (Polychromatic418967fa.accept_19_6_12_13_1_14522 63 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 145 241 (accept_3_3 62 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 145 241 (Polychromatic418967fa.accept_13_9_2_7_1_1083 61 145 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 241 (accept_3_3 59 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58
  145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 241 (accept_3_3 56 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 241 (Polychromatic418967fa.accept_20_15_5_1_1_5899 55 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 241 (accept_3_3 53 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 52 145
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 241 (accept_3_3 50 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 241 (accept_3_3 47 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 241 (Polychromatic418967fa.accept_10_6_5_1_1_482 46 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 241
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 241 (accept_3_3 44 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 241 (accept_3_3 41 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 241 (accept_3_3 38 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 241 (accept_3_3 35 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 34 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 241 (accept_3_3 32 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 241 (accept_3_3 29 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 28 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 241
  (Polychromatic418967fa.accept_17_10_9_3_1_7144 27 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 241 (accept_3_3 26 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 241 (Polychromatic418967fa.accept_19_6_12_13_1_14522 25 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 241 (accept_3_3 23 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 241 (accept_3_3 20 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 241 (accept_3_3 17 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 241 (accept_3_3 14 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 241 (accept_3_3 11 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 241 (Polychromatic418967fa.accept_17_10_9_3_1_7144 10 145 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 241 (accept_3_3 8 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 241 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 241 (accept_3_3 5 145 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 145 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 241 (accept_3_3 2 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  144 241 (Eq.refl Bool.true) (allA_succ_of_accept 97 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 144 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 144 241
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 96 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 144 241 (accept_3_3 95 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 144 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 94 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 144 241 (Polychromatic418967fa.accept_19_17_11_13_1_4840 93 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 144 241 (accept_3_3 92 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 144 241 (Polychromatic418967fa.accept_14_7_4_3_1_488 91 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 144 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 90 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 144 241 (accept_3_3 89 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 144 241 (Polychromatic418967fa.accept_19_12_11_13_1_4885 88 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 144 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 87 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 144 241 (accept_3_3 86 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 144 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 144 241
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 84 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 144 241 (accept_3_3 83 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 144 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 82 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 144 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 241 (accept_3_3 80 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 144 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 79 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 144 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 144 241 (accept_3_3 77 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 144 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 241 (accept_3_3 74 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 144 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 73 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 144 241
  (Polychromatic418967fa.accept_21_9_18_10_1_5388 72 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 144 241 (accept_3_3 71 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 144 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 144 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 144 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 241 (accept_3_3 68 144 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  67 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 241
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 66 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 144 241 (accept_3_3 65 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 144 241 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 241 (accept_3_3 62 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 241 (Polychromatic418967fa.accept_22_17_12_21_1_14521 61
  144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 241
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 60 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 144 241 (accept_3_3 59 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 144 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 58 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 241 (accept_3_3 56 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 241
  (Polychromatic418967fa.accept_19_16_11_13_1_4944 54 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 144 241 (accept_3_3 53 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 144 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 144 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 241 (Polychromatic418967fa.accept_15_6_9_1_1_1823 51 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 241 (accept_3_3 50 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 241
  (Polychromatic418967fa.accept_14_7_4_3_1_488 49 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 144 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 241 (accept_3_3 47 144 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 144 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 46 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 241
  (Polychromatic418967fa.accept_10_5_4_1_1_842 45 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 144 241 (accept_3_3 44 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 144 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 42 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 241 (accept_3_3 41 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 241
  (Polychromatic418967fa.accept_17_5_8_3_1_1419 39 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 144 241 (accept_3_3 38 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 144 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 241 (accept_3_3 35 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 241
  (Polychromatic418967fa.accept_22_11_12_21_1_14520 33 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 144 241 (accept_3_3 32 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 144 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 144 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 241 (Polychromatic418967fa.accept_17_13_8_3_1_7177 30 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 241 (accept_3_3 29 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 241
  (Polychromatic418967fa.accept_21_7_18_10_1_14519 28 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 241 (accept_3_3 26 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 241
  (Polychromatic418967fa.accept_11_2_1_10_1_196 24 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 144 241 (accept_3_3 23 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 241 (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 241 (accept_3_3 20 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 241 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 144
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 241
  (Polychromatic418967fa.accept_23_18_6_11_1_14518 18 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 241 (accept_3_3 17 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 144 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 241 (accept_3_3 14 144 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 241 (Polychromatic418967fa.accept_7_6_4_3_1_266
  13 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 241
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 12 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 144 241 (accept_3_3 11 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 144 241 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 144 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 241 (accept_3_3 8 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 144 241 (accept_3_3 5 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  144 241 (Polychromatic418967fa.accept_27_4_9_25_1_14517 4 144 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 144 241 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 241 (accept_3_3 2 144 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  143 241 (Eq.refl Bool.true) (allA_of_3_1 99 143 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 142 241
  (Eq.refl Bool.true) (allA_succ_of_accept 99 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 142 241 (accept_3_3 98 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 142 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 142 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 96 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 142 241 (accept_3_3 95 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 142 241 (Polychromatic418967fa.accept_17_9_6_3_1_2398 94 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 142 241 (accept_3_3 92 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 142 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 90 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 142 241 (accept_3_3 89 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 142 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 88 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 142 241 (accept_3_3 86 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 142 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 142 241
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 142 241 (accept_3_3 83 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 142 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 142 241 (accept_3_3 80 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 142 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 142 241 (accept_3_3 77 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 142 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 142 241 (accept_3_3 74 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 142 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 73 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 142 241
  (Polychromatic418967fa.accept_19_15_9_13_1_4838 72 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 142 241 (accept_3_3 71 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 142 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 70 142 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 142 241 (accept_3_3 68 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 142 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 66 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 142 241 (accept_3_3 65 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 241 (accept_3_3 62 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 241
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 241 (accept_3_3 59 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 241 (Polychromatic418967fa.accept_13_6_12_7_1_5131 58 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 241 (accept_3_3 56 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 241 (accept_3_3 53 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 241 (accept_3_3 50 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 49 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 241 (accept_3_3 47 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 241 (accept_3_3 44 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 241
  (Polychromatic418967fa.accept_19_4_9_13_1_7792 42 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 241 (accept_3_3 41 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 241 (accept_3_3 38 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 241 (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 241 (accept_3_3 35 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 241 (accept_3_3 32 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 241
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 241 (accept_3_3 29 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 241 (accept_3_3 26 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 241 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 241
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 142 241 (accept_3_3 23 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 142 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 142 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 241 (accept_3_3 20 142 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 241
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 241 (accept_3_3 17 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 241 (accept_3_3 14 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 241 (accept_3_3 11 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 241 (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 241 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 241 (accept_3_3 8 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 241 (accept_3_3 5 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 142 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 241 (accept_3_3 2 142 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 142 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 141 241 (Eq.refl Bool.true) (allA_succ_of_accept 100 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 141
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 141 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 99 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 141 241 (accept_3_3 98 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 141 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 97 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 141 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 241 (accept_3_3 95 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 141 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 141 241 (accept_3_3 92 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 141 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 141 241 (Polychromatic418967fa.accept_13_12_11_7_1_2491 90 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 241 (accept_3_3 89 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 141 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 141 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 87 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 141 241 (accept_3_3 86 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 141 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 85 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 141 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 241 (accept_3_3 83 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 141 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 141 241 (accept_3_3 80 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 141 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 141 241 (Polychromatic418967fa.accept_11_1_9_10_1_184 78 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 241 (accept_3_3 77 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 141 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 141 241 (accept_3_3 74 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 141 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 141 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 241 (accept_3_3 71 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 241
  (Polychromatic418967fa.accept_13_4_11_7_1_558 69 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 141 241 (accept_3_3 68 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 141 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 141 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 241 (accept_3_3 65 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 241
  (Polychromatic418967fa.accept_11_8_9_10_1_503 63 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 141 241 (accept_3_3 62 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 141 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 141 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 241 (accept_3_3 59 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 241 (accept_3_3 56 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 141 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 241 (accept_3_3 53 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 241 (accept_3_3 50 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 141 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 241 (accept_3_3 47 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 241
  (Polychromatic418967fa.accept_11_1_9_10_1_184 45 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 241 (accept_3_3 44 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 241 (Polychromatic418967fa.accept_13_4_11_7_1_558 43 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 241 (Polychromatic418967fa.accept_13_3_11_7_1_2488 42 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 241 (accept_3_3 41 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 241 (accept_3_3 38 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 241 (accept_3_3 35 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 241 (accept_3_3 32 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 241 (accept_3_3 29 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 241 (accept_3_3 26 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 241 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 241 (accept_3_3 23 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 241 (accept_3_3 20 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 241 (accept_3_3 17 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 241
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 241 (accept_3_3 14 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 241 (accept_3_3 11 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 241 (accept_3_3 8 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 241 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 241 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 241 (accept_3_3 5 141 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 241 (accept_3_3 2 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 141 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 140 241 (Eq.refl Bool.true) (allA_of_3_1 102 140 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 139
  241 (Eq.refl Bool.true) (allA_succ_of_accept 102 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 139 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 139 241 (accept_3_3 101 139 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 139 241 (Polychromatic418967fa.accept_7_2_6_3_1_100
  100 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 139 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 99 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 139 241 (accept_3_3 98 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 139 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 97 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 139 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 241 (accept_3_3 95 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 93 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 241 (accept_3_3 92 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 241 (accept_3_3 89 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 87 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 241 (accept_3_3 86 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 85 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 241 (accept_3_3 83 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 81 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 241 (accept_3_3 80 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 241 (accept_3_3 77 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 241 (Polychromatic418967fa.accept_13_11_9_7_1_2484 76 139 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 241 (accept_3_3 74 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 241 (accept_3_3 71 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 69 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 241 (accept_3_3 68 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 241 (accept_3_3 65 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 241
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 241 (accept_3_3 62 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 241 (Polychromatic418967fa.accept_19_4_6_13_1_6335 61 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 241 (accept_3_3 59 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 241 (accept_3_3 56 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 241 (accept_3_3 53 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 241 (Polychromatic418967fa.accept_10_2_9_1_1_185 52 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 241 (accept_3_3 50 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 241 (Polychromatic418967fa.accept_19_11_6_13_1_3477 49 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 241 (accept_3_3 47 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 241
  (Polychromatic418967fa.accept_10_5_9_1_1_187 45 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 241 (accept_3_3 44 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 241 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 241 (accept_3_3 41 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 241 (Polychromatic418967fa.accept_18_4_13_7_1_5395 40 139 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 241 (accept_3_3 38 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 241 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 241 (accept_3_3 35 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 241 (accept_3_3 32 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 241 (Polychromatic418967fa.accept_16_15_11_1_1_7767 31 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 241 (accept_3_3 29 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 241
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 241 (accept_3_3 26 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 241 (accept_3_3 23 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 241 (accept_3_3 20 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 241 (accept_3_3 17 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 241
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 241 (accept_3_3 14 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 241 (Polychromatic418967fa.accept_22_13_7_21_1_8339 13 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 241 (accept_3_3 11 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 241 (accept_3_3 8 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 241 (Polychromatic418967fa.accept_19_7_6_13_1_6322 7 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 241 (accept_3_3 5 139 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 241
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 241 (accept_3_3 2 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 138 241 (Eq.refl Bool.true) (allA_succ_of_accept 103 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 138
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 138 241
  (Polychromatic418967fa.accept_19_7_5_13_1_3493 102 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 138 241 (accept_3_3 101 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 138 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 100 138 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 138 241 (accept_3_3 98 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 138 241
  (Polychromatic418967fa.accept_20_17_18_1_1_8880 97 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 138 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 96 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 138 241 (accept_3_3 95 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 138 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 138 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 93 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 138 241 (accept_3_3 92 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 138 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 90 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 138 241 (accept_3_3 89 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 138 241 (Polychromatic418967fa.accept_13_10_8_7_1_1074 88 138
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 138 241 (accept_3_3 86 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 138 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 138 241 (Polychromatic418967fa.accept_19_8_5_13_1_7800 84 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 138 241 (accept_3_3 83 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 138 241
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 138 241 (accept_3_3 80 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 138 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 138 241 (accept_3_3 77 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 138 241 (accept_3_3 74 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 138 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 138 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 138 241 (accept_3_3 71 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 241 (Polychromatic418967fa.accept_25_20_13_16_1_14516 70 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 138 241 (accept_3_3 68 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 138 241 (Polychromatic418967fa.accept_13_1_8_7_1_1088 66 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 138 241 (accept_3_3 65 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 138 241 (accept_3_3 62 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 138 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 138 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 138 241 (accept_3_3 59 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 241
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 138 241 (accept_3_3 56 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 138 241 (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 138 241 (accept_3_3 53 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 241 (Polychromatic418967fa.accept_17_1_2_3_1_4668 52 138
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 138 241 (accept_3_3 50 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 138 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 138 241 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 138 241 (accept_3_3 47 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 241
  (Polychromatic418967fa.accept_17_11_2_3_1_8468 45 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 138 241 (accept_3_3 44 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 138 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 241 (accept_3_3 41 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 138 241 (accept_3_3 38 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 138 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 138 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 241 (accept_3_3 35 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 241 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 138 241 (accept_3_3 32 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 138 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 241 (accept_3_3 29 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 138 241 (accept_3_3 26 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 138 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 138 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 241 (accept_3_3 23 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 241
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 138 241 (accept_3_3 20 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 138 241 (Polychromatic418967fa.accept_17_1_2_3_1_4668 18 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 241 (accept_3_3 17 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 138 241 (accept_3_3 14 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 138 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 241 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 241 (accept_3_3 11 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 138 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 241
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 241 (accept_3_3 8 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 241 (accept_3_3 5 138 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 138 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 241 (accept_3_3 2 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 138 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 137 241 (Eq.refl Bool.true) (allA_of_3_1 105 137 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 136 241 (Eq.refl Bool.true) (allA_succ_of_accept 105 136 241 (Polychromatic418967fa.accept_6_3_4_1_1_8
  105 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 136 241 (accept_3_3
  104 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 136 241
  (Polychromatic418967fa.accept_9_4_1_7_1_293 103 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 136 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 102 136 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 136 241 (accept_3_3 101 136 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 136 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 100 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 136 241 (accept_3_3 98 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 136 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 97 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 136 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 96 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 136 241 (accept_3_3 95 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 136 241 (accept_3_3 92 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 136 241 (Polychromatic418967fa.accept_14_7_10_3_1_1034 91 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 136 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 90 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 136 241 (accept_3_3 89 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 136 241 (Polychromatic418967fa.accept_19_12_3_13_1_4911 88 136
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 136 241 (accept_3_3 86 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 136 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 136 241 (accept_3_3 83 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 136 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 136 241 (accept_3_3 80 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 136 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 79 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 136 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 136 241 (accept_3_3 77 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 136 241 (accept_3_3 74 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 136 241 (Polychromatic418967fa.accept_16_9_8_1_1_1228 73 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 136 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 136 241 (accept_3_3 71 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 136 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 136
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 136 241 (accept_3_3 68 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 136 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 136 241 (accept_3_3 65 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 136 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 64 136 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 136 241 (accept_3_3 62 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 136 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 136 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 136 241 (accept_3_3 59 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 136 241 (accept_3_3 56 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 136 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 55 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 136 241 (Polychromatic418967fa.accept_19_16_3_13_1_11816 54 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 241 (accept_3_3 53 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 136 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 136
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 136 241 (accept_3_3 50 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 136 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 241 (accept_3_3 47 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 136 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 136 241 (accept_3_3 44 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 136 241 (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 136 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 241 (accept_3_3 41 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 136 241 (accept_3_3 38 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 136 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 136 241 (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 241 (accept_3_3 35 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 136 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 136
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 136 241 (accept_3_3 32 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 136 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 241 (accept_3_3 29 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 241 (Polychromatic418967fa.accept_16_12_8_1_1_5270 28 136 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 136 241 (accept_3_3 26 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 136 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 136 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 241 (accept_3_3 23 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 241 (accept_3_3 20 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 241 (Polychromatic418967fa.accept_23_19_21_11_1_14515 19 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 241 (Polychromatic418967fa.accept_20_18_16_1_1_8850 18 136 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 241 (accept_3_3 17 136 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 241 (Polychromatic418967fa.accept_11_5_4_10_1_524
  16 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 241 (accept_3_3 14 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 241 (accept_3_3 11 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 241 (accept_3_3 8 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 241 (accept_3_3 5 136 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 136 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 241 (accept_3_3 2 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 136 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 135 241 (Eq.refl Bool.true) (allA_succ_of_accept 106 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2
  106 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 135 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 105 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 135 241 (accept_3_3 104 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 135 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 103 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 241 (accept_3_3 101 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 135 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 99 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 135 241 (accept_3_3 98 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 135 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 97 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 135 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 96 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 241 (accept_3_3 95 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 93 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 135 241 (accept_3_3 92 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 135 241 (Polychromatic418967fa.accept_19_15_2_13_1_10598 91 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 241 (accept_3_3 89 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 135 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 241
  (Polychromatic418967fa.accept_19_11_2_13_1_4907 87 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 241 (accept_3_3 86 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 135 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 85 135 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 84 135
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 241 (accept_3_3 83 135
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2
  82 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 135 241 (accept_3_3 80 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 135 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 79 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 241 (accept_3_3 77 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 135 241 (accept_3_3 74 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 135 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 73 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 241 (Polychromatic418967fa.accept_16_8_7_1_1_8875 72 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 241 (accept_3_3 71 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 135 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 241 (accept_3_3 68 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 135 241 (Polychromatic418967fa.accept_13_2_5_7_1_1695 67 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 241 (accept_3_3 65 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 241
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 135 241 (accept_3_3 62 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 135 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 135 241 (Polychromatic418967fa.accept_18_6_9_7_1_2905 60 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 241 (accept_3_3 59 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 135 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 241 (accept_3_3 56 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 135 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 241 (accept_3_3 53 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 241
  (Polychromatic418967fa.accept_11_7_3_10_1_1461 51 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 135 241 (accept_3_3 50 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 135 241 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 135 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 241 (accept_3_3 47 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 241 (accept_3_3 44 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 241 (accept_3_3 41 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 241 (accept_3_3 38 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 241 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 241 (accept_3_3 35 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 241
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 241 (accept_3_3 32 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 241 (Polychromatic418967fa.accept_23_8_20_11_1_14514 31 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 241 (accept_3_3 29 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 241
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 241 (accept_3_3 26 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 241 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 241 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 241 (accept_3_3 23 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 241 (accept_3_3 20 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 241 (accept_3_3 17 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 241
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 241 (accept_3_3 14 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 241 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 241 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 241 (accept_3_3 11 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 241
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 241 (accept_3_3 8 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 241 (accept_3_3 5 135 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 241
  (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 241 (accept_3_3 2 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 241 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 134 241 (Eq.refl Bool.true) (allA_of_3_1 108 134 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 133 241 (Eq.refl Bool.true) (allA_succ_of_accept 108 133 241
  (Polychromatic418967fa.accept_8_4_5_1_1_299 108 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 133 241 (accept_3_3 107 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 133 241 (Polychromatic418967fa.accept_21_1_7_10_1_2596 106 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 105 133 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 105 133 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 133 241 (accept_3_3 104 133 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 133 241
  (Polychromatic418967fa.accept_20_3_13_1_1_8886 103 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 133 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 102 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 241 (accept_3_3 101 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 100 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 133 241
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 99 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 133 241 (accept_3_3 98 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 133 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 97 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 133 241 (Polychromatic418967fa.accept_17_11_14_3_1_1427 96 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 133 241 (accept_3_3 95 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 133 241 (Polychromatic418967fa.accept_14_10_7_3_1_1022 94 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 133 241
  (Polychromatic418967fa.accept_15_3_13_1_1_479 93 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 133 241 (accept_3_3 92 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 133 241 (Polychromatic418967fa.accept_17_6_14_3_1_4678 91 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 133 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 90 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 241 (accept_3_3 89 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 88 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 133 241
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 87 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 133 241 (accept_3_3 86 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 133 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 133 241 (accept_3_3 83 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 82 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 241
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 81 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 241 (accept_3_3 80 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 79 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 78 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 133 241 (accept_3_3 77 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 76 133 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 241
  (Polychromatic418967fa.accept_11_9_1_10_1_920 75 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 133 241 (accept_3_3 74 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 133 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 133 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 241 (accept_3_3 71 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 133 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 241
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 69 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 241 (accept_3_3 68 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 241 (Polychromatic418967fa.accept_14_11_7_3_1_3416 67 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 66 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 241 (accept_3_3 65 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 64 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 241
  (Polychromatic418967fa.accept_13_11_3_7_1_2513 63 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 241 (accept_3_3 62 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 241 (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 241 (accept_3_3 59 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 58 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 241
  (Polychromatic418967fa.accept_11_2_1_10_1_196 57 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 241 (accept_3_3 56 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 241 (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 241 (Polychromatic418967fa.accept_16_6_5_1_1_7761 54 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 241 (accept_3_3 53 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 133 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 241
  (Polychromatic418967fa.accept_21_9_7_10_1_3907 51 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 241 (accept_3_3 50 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 241 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 241 (accept_3_3 47 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 46 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 241
  (Polychromatic418967fa.accept_16_13_5_1_1_3017 45 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 241 (accept_3_3 44 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 241 (accept_3_3 41 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 241
  (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 241 (accept_3_3 38 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 241 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 241 (accept_3_3 35 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 241 (Polychromatic418967fa.accept_13_8_3_7_1_2455 34 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 241
  (Polychromatic418967fa.accept_15_3_13_1_1_479 33 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 241 (accept_3_3 32 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 241 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 241 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 241 (accept_3_3 29 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 133 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 241
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 241 (accept_3_3 26 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 241 (Polychromatic418967fa.accept_14_11_7_3_1_3416 25 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 241 (accept_3_3 23 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 22 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 241
  (Polychromatic418967fa.accept_13_8_3_7_1_2455 21 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 241 (accept_3_3 20 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 241 (Polychromatic418967fa.accept_17_2_14_3_1_4679 19 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 241 (accept_3_3 17 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 241 (Polychromatic418967fa.accept_21_16_7_10_1_8601 16 133
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 241
  (Polychromatic418967fa.accept_16_15_5_1_1_7724 15 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 241 (accept_3_3 14 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 241 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 241 (accept_3_3 11 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 241 (Polychromatic418967fa.accept_13_10_3_7_1_2517 10 133 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 241
  (Polychromatic418967fa.accept_11_9_1_10_1_920 9 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 241 (accept_3_3 8 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 241 (Polychromatic418967fa.accept_23_7_18_11_1_14513 7 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 241 (Polychromatic418967fa.accept_16_6_5_1_1_7761 6 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 241 (accept_3_3 5 133 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 241 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 133 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 241
  (Polychromatic418967fa.accept_15_3_13_1_1_479 3 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 241 (accept_3_3 2 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 241 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 133 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 132 241 (Eq.refl Bool.true) (allA_succ_of_accept 109 132 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 109 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 132 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 108 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 132 241 (accept_3_3 107 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 132 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 106 132 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 132 241
  (Polychromatic418967fa.accept_23_13_17_11_1_14512 105 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 132 241 (accept_3_3 104 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 132 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 102 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 132 241 (accept_3_3 101 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 132 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 100 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 132 241 (Polychromatic418967fa.accept_10_9_2_1_1_840 99 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 132 241 (accept_3_3 98 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 132 241 (Polychromatic418967fa.accept_23_5_17_11_1_8012 97 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 132 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 96 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 132 241 (accept_3_3 95 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 132 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 94 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 132 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 93 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 132 241 (accept_3_3 92 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 132 241
  (Polychromatic418967fa.accept_19_14_18_13_1_7823 90 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 132 241 (accept_3_3 89 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 88 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 241 (Polychromatic418967fa.accept_13_9_2_7_1_1083 87 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 241 (accept_3_3 86 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 241
  (Polychromatic418967fa.accept_8_5_4_1_1_111 85 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 132 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 132 241 (accept_3_3 83 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271
  81 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 241 (accept_3_3 80
  132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 132 241 (Polychromatic418967fa.accept_16_14_4_1_1_3049 78 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 241 (accept_3_3 77 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 132 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 241 (Polychromatic418967fa.accept_9_3_6_7_1_562
  75 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 241 (accept_3_3 74
  132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 241
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 132 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 132 241 (accept_3_3 71 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 132 241 (Polychromatic418967fa.accept_13_5_2_7_1_2414 70 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 241
  (Polychromatic418967fa.accept_8_5_4_1_1_111 69 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 132 241 (accept_3_3 68 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 132 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 241 (accept_3_3 65 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 241
  (Polychromatic418967fa.accept_10_3_2_1_1_839 63 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 132 241 (accept_3_3 62 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 132 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 241 (accept_3_3 59 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 132 241 (accept_3_3 56 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 132 241 (Polychromatic418967fa.accept_19_16_18_13_1_4855 54 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 132 241 (accept_3_3 53 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 132 241 (accept_3_3 50 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 132 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 132 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 241 (accept_3_3 47 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 241
  (Polychromatic418967fa.accept_8_5_4_1_1_111 45 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 132 241 (accept_3_3 44 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 132 241 (Polychromatic418967fa.accept_10_3_2_1_1_839 43 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 132 241 (Polychromatic418967fa.accept_17_8_13_3_1_3432 42 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 241 (accept_3_3 41 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 132 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 241
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 132 241 (accept_3_3 38 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 132 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 132 241 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 241 (accept_3_3 35 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 241 (Polychromatic418967fa.accept_13_8_2_7_1_2452 34 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 241
  (Polychromatic418967fa.accept_10_3_2_1_1_839 33 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 132 241 (accept_3_3 32 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 132 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 132 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 241 (accept_3_3 29 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 241
  (Polychromatic418967fa.accept_17_10_13_3_1_1425 27 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 132 241 (accept_3_3 26 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 241 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 241 (accept_3_3 23 132
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 241
  (Polychromatic418967fa.accept_9_4_6_7_1_286 22 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 132 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 241 (accept_3_3 20 132 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271
  18 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 241 (accept_3_3 17
  132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 241
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 132 241 (Polychromatic418967fa.accept_21_15_6_10_1_10016 15 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 241 (accept_3_3 14 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 241 (accept_3_3 11 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 241 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 241 (accept_3_3 8 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 241 (Polychromatic418967fa.accept_23_7_17_11_1_6135 7 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 241
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 241 (accept_3_3 5 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 241 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 132 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 241 (accept_3_3 2 132 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 131 241 (Eq.refl Bool.true) (allA_of_3_1 111 131 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 130 241 (Eq.refl Bool.true) (allA_succ_of_accept 111 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 111 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 130 241 (accept_3_3 110 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 109 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 130 241 (Polychromatic418967fa.accept_16_12_2_1_1_1215 108 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 130 241 (accept_3_3 107 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 106 130
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 130 241 (accept_3_3 104 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 130 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 102 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 130 241 (accept_3_3 101 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 100 130 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 130 241 (accept_3_3 98 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 130 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 96 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 130 241 (accept_3_3 95 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 130 241 (Polychromatic418967fa.accept_17_9_11_3_1_2353 94 130 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 130 241 (accept_3_3 92 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 90 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 130 241 (accept_3_3 89 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 130 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 88 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 130 241 (accept_3_3 86 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 130 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 84 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 130 241 (accept_3_3 83 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 82 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 130 241 (accept_3_3 80 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 130 241 (accept_3_3 77 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 130 241 (accept_3_3 74 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 130 241 (Polychromatic418967fa.accept_19_15_16_13_1_1336 72 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 130 241 (accept_3_3 71 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 130 241 (Polychromatic418967fa.accept_16_6_2_1_1_4081 70 130
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 130 241 (accept_3_3 68 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 130 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 130 241 (accept_3_3 65 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 130 241 (accept_3_3 62 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 130 241 (Polychromatic418967fa.accept_17_10_11_3_1_3442 61 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 130 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 60 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 130 241 (accept_3_3 59 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 241 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 130 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 241 (accept_3_3 56 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 130 241 (Polychromatic418967fa.accept_15_9_10_1_1_1062 54 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 241 (accept_3_3 53 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 130 241 (Polychromatic418967fa.accept_11_8_9_10_1_503 52 130
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 130 241 (accept_3_3 50 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 130 241 (Polychromatic418967fa.accept_14_7_4_3_1_488 49 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 241 (accept_3_3 47 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 130 241 (accept_3_3 44 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 241 (accept_3_3 41 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 130 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 130 241 (accept_3_3 38 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 241 (accept_3_3 35 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 241 (accept_3_3 32 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 130 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 241 (accept_3_3 29 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 241 (accept_3_3 26 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 241 (Polychromatic418967fa.accept_16_9_2_1_1_3077 25 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 241 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 241 (accept_3_3 23 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 241 (accept_3_3 20 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 241 (Polychromatic418967fa.accept_19_18_16_13_1_10572 18 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 241 (accept_3_3 17 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 130
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 241 (accept_3_3 14 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 241 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 241 (accept_3_3 11 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 241 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 241 (accept_3_3 8 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 241 (accept_3_3 5 130 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 241 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 241 (accept_3_3 2 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 130 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 129 241 (Eq.refl Bool.true) (allA_succ_of_accept 112 129 241
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 129 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 111 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 129 241 (accept_3_3 110 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 109 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 241 (Polychromatic418967fa.accept_10_8_9_1_1_189
  108 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 241 (accept_3_3
  107 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 241
  (Polychromatic418967fa.accept_6_4_3_1_1_57 106 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 129 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 105 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 241 (accept_3_3 104 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 129 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 103 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 241
  (Polychromatic418967fa.accept_10_2_9_1_1_185 102 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 129 241 (accept_3_3 101 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 129 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 99 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 241 (accept_3_3 98 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 97 129
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 96 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 129 241 (accept_3_3 95 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 129 241 (Polychromatic418967fa.accept_19_17_15_13_1_7794 93 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 241 (accept_3_3 92 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 241
  (Polychromatic418967fa.accept_19_14_15_13_1_4898 90 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 129 241 (accept_3_3 89 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 241 (accept_3_3 86 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  85 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 241
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 84 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 241 (accept_3_3 83 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 241 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 241 (accept_3_3 80 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 241 (Polychromatic418967fa.accept_17_11_10_3_1_2364 79 129
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 241 (accept_3_3 77 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 241 (accept_3_3 74 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 241
  (Polychromatic418967fa.accept_10_2_9_1_1_185 72 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 129 241 (accept_3_3 71 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 129 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 241 (accept_3_3 68 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 241
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 66 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 241 (accept_3_3 65 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 241 (accept_3_3 62 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 241 (Polychromatic418967fa.accept_19_4_15_13_1_13215 61
  129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 241 (accept_3_3 59 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 241 (Polychromatic418967fa.accept_13_5_12_7_1_1080 57 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 241 (accept_3_3 56 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 241
  (Polychromatic418967fa.accept_19_16_15_13_1_1335 54 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 241 (accept_3_3 53 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 241 (accept_3_3 50 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  49 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 241
  (Polychromatic418967fa.accept_10_8_9_1_1_189 48 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 241 (accept_3_3 47 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 241 (accept_3_3 44 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 241 (Polychromatic418967fa.accept_13_4_12_7_1_2439 43 129
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 241 (accept_3_3 41 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 241 (accept_3_3 38 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 241
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 241 (accept_3_3 35 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 129 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 241 (accept_3_3 32 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 241 (Polychromatic418967fa.accept_9_4_3_7_1_296
  31 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 241
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 241 (accept_3_3 29 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 241 (accept_3_3 26 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 241 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 129
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 241 (accept_3_3 23 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 241 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 241 (accept_3_3 20 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 129 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 241
  (Polychromatic418967fa.accept_10_8_9_1_1_189 18 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 241 (accept_3_3 17 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 241 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 241 (accept_3_3 14 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 241 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 241
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 241 (accept_3_3 11 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 241 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 241 (accept_3_3 8 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 241 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 241
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 241 (accept_3_3 5 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 241 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 241 (accept_3_3 2 129 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 241 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 129 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 114 128 241 (Eq.refl Bool.true) (allA_of_3_1 114 128 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 115 127 241 (Eq.refl Bool.true) (allA_succ_of_accept 114 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2
  114 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 127 241 (accept_3_3
  113 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 127 241
  (Polychromatic418967fa.accept_9_4_1_7_1_293 112 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 127 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 111 127 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 127 241 (accept_3_3 110 127 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 127 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 109 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 127 241
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 108 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 127 241 (accept_3_3 107 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 127 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 127 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 105 127
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 127 241 (accept_3_3 104 127
  241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 127 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 103 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 127 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 127 241 (accept_3_3 101 127 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 127 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 100 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 127 241
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 99 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 127 241 (accept_3_3 98 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 127 241 (Polychromatic418967fa.accept_17_12_8_3_1_4646 97 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 127 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 96 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 241 (accept_3_3 95 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 93 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 241 (accept_3_3 92 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 241 (Polychromatic418967fa.accept_16_11_15_1_1_2074 91 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 241 (accept_3_3 89 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 241 (accept_3_3 86 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 241 (accept_3_3 83 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 241 (accept_3_3 80 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 241 (accept_3_3 77 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 241 (accept_3_3 74 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 241 (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 241 (accept_3_3 71 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 241 (accept_3_3 68 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 241 (accept_3_3 65 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 241 (Polychromatic418967fa.accept_10_4_7_1_1_471 64 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 241
  (Polychromatic418967fa.accept_17_12_8_3_1_4646 63 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 241 (accept_3_3 62 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 241 (accept_3_3 59 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 241 (accept_3_3 56 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 241 (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 241 (accept_3_3 53 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 241 (Polychromatic418967fa.accept_18_16_1_7_1_4083 52 127 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 241 (accept_3_3 50 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 241 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 241 (accept_3_3 47 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 241
  (Polychromatic418967fa.accept_21_3_1_10_1_10008 45 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 127 241 (accept_3_3 44 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 127 241 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 127 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 241 (accept_3_3 41 127 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 241 (Polychromatic418967fa.accept_7_5_1_3_1_103
  40 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 241
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 241 (accept_3_3 38 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 241 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 241 (accept_3_3 35 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 241
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 241 (accept_3_3 32 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 241 (accept_3_3 29 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 241 (Polychromatic418967fa.accept_20_8_7_1_1_3024 28 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 241
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 241 (accept_3_3 26 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 241 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 241 (accept_3_3 23 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 241 (accept_3_3 20 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 241 (accept_3_3 17 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 241 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 241
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 241 (accept_3_3 14 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 241 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 241 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 241 (accept_3_3 11 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 241
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 241 (accept_3_3 8 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 241 (Polychromatic418967fa.accept_21_7_1_10_1_8571 7 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 241 (accept_3_3 5 127 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 241 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 241
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 241 (accept_3_3 2 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 241 (Polychromatic418967fa.accept_22_1_17_21_1_8330 1 127 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 126 241 (Eq.refl Bool.true) (allA_succ_of_accept 115 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 115 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 126 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 114 126 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 126 241 (accept_3_3 113 126 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 112 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 112 126 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 111 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 126 241 (accept_3_3 110 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 126 241 (Polychromatic418967fa.accept_16_13_14_1_1_2094 109 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 108 126 241 (Polychromatic418967fa.accept_13_4_9_7_1_2402 108 126 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 126 241 (accept_3_3 107 126 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 126 241 (Polychromatic418967fa.accept_13_2_9_7_1_164
  106 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 126 241
  (Polychromatic418967fa.accept_10_5_6_1_1_836 105 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 126 241 (accept_3_3 104 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 103 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 102 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 126 241 (accept_3_3 101 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 126 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 100
  126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 99 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 126 241 (accept_3_3 98 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 126 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 97 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 126 241 (Polychromatic418967fa.accept_19_1_12_13_1_6279 96 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 126 241 (accept_3_3 95 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 94 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 241
  (Polychromatic418967fa.accept_13_2_9_7_1_164 93 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 126 241 (accept_3_3 92 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 91 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 126 241 (Polychromatic418967fa.accept_19_14_12_13_1_3485 90 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 241 (accept_3_3 89 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 241 (Polychromatic418967fa.accept_24_16_6_1_1_9516 88 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 87 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 126 241 (accept_3_3 86 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 126 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 85 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 126 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 84 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 126 241 (accept_3_3 83 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 82 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 241
  (Polychromatic418967fa.accept_11_4_5_10_1_926 81 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 126 241 (accept_3_3 80 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 126 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 78 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 126 241 (accept_3_3 77 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 241 (Polychromatic418967fa.accept_13_11_9_7_1_2484 76 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 126 241 (accept_3_3 74 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 126 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 73 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 241 (accept_3_3 71 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 70 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 241
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 126 241 (accept_3_3 68 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 126 241 (Polychromatic418967fa.accept_24_18_6_1_1_11229 66 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 241 (accept_3_3 65 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 241 (Polychromatic418967fa.accept_22_20_16_21_1_9852 64
  126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 126 241 (accept_3_3 62 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 126 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 61 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 126 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 241 (accept_3_3 59 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 241 (Polychromatic418967fa.accept_13_6_9_7_1_2430 58 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 241
  (Polychromatic418967fa.accept_10_7_6_1_1_486 57 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 126 241 (accept_3_3 56 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 126 241 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 241 (accept_3_3 53 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 126 241 (accept_3_3 50 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 126 241 (Polychromatic418967fa.accept_19_11_12_13_1_4844 49 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 48 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 241 (accept_3_3 47 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 241 (Polychromatic418967fa.accept_17_12_7_3_1_1498 46 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 241
  (Polychromatic418967fa.accept_10_5_6_1_1_836 45 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 126 241 (accept_3_3 44 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 241 (accept_3_3 41 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 40 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 126 241 (accept_3_3 38 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 126 241 (Polychromatic418967fa.accept_10_7_6_1_1_486 37 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 126 241 (Polychromatic418967fa.accept_16_4_14_1_1_1241 36 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 241 (accept_3_3 35 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 241 (Polychromatic418967fa.accept_13_8_9_7_1_530 34 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 241
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 126 241 (accept_3_3 32 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 126 241 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 241 (accept_3_3 29 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 28 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 126 241 (accept_3_3 26 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 126 241 (Polychromatic418967fa.accept_10_5_6_1_1_836 25 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 126 241 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 241 (accept_3_3 23 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 241
  (Polychromatic418967fa.accept_13_8_9_7_1_530 21 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 126 241 (accept_3_3 20 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 126 241 (Polychromatic418967fa.accept_15_3_6_1_1_1834 18 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 241 (accept_3_3 17 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 241 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 126 241 (accept_3_3 14 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 126 241 (Polychromatic418967fa.accept_16_13_14_1_1_2094 13 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 126 241 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 241 (accept_3_3 11 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 241 (Polychromatic418967fa.accept_15_10_6_1_1_3707 10 126
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 241
  (Polychromatic418967fa.accept_15_9_6_1_1_493 9 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 126 241 (accept_3_3 8 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  126 241 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 126 241 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 241 (accept_3_3 5 126 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 241 (Polychromatic418967fa.accept_11_4_5_10_1_926 4 126 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 241
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 126 241 (accept_3_3 2 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  126 241 (Polychromatic418967fa.accept_19_1_12_13_1_6279 1 126 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 117 125 241 (Eq.refl Bool.true) (allA_of_3_1 117 125 241 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 118 124 241 (Eq.refl Bool.true) (allA_succ_of_accept 117 124 241 (Polychromatic418967fa.accept_6_3_4_1_1_8
  117 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 124 241 (accept_3_3
  116 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 124 241
  (Polychromatic418967fa.accept_10_5_4_1_1_842 115 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 114 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 114 124 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 124 241 (accept_3_3 113 124 241 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 112 124 241 (Polychromatic418967fa.accept_18_4_16_7_1_1873 112 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 111 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 124 241 (accept_3_3 110 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 124 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 109 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 124 241 (Polychromatic418967fa.accept_15_3_4_1_1_1072 108 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 124 241 (accept_3_3 107 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 106 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 124 241 (accept_3_3 104 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 124 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 103 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 124 241 (Polychromatic418967fa.accept_15_12_4_1_1_3746 102 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 124 241 (accept_3_3 101 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98
  100 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 124 241 (accept_3_3 98 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 124 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 97 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 124 241 (Polychromatic418967fa.accept_19_1_10_13_1_4880 96 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 124 241 (accept_3_3 95 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 124 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 94 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 124 241 (accept_3_3 92 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 124 241 (Polychromatic418967fa.accept_16_11_12_1_1_3001 91 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 124 241 (Polychromatic418967fa.accept_20_10_4_1_1_8840 90 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 124 241 (accept_3_3 89 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 124 241 (Polychromatic418967fa.accept_16_8_12_1_1_7720 88 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 124 241 (accept_3_3 86 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 85 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 124 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 84 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 241 (accept_3_3 83 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 124 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 82 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 124 241 (accept_3_3 80 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 78 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 241 (accept_3_3 77 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 124 241 (Polychromatic418967fa.accept_17_8_5_3_1_2397 76 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 124 241 (accept_3_3 74 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 124 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 73 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 241 (accept_3_3 71 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 124 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 124 241 (accept_3_3 68 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 124 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 67 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 124 241 (Polychromatic418967fa.accept_16_2_12_1_1_3086 66 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 124 241 (accept_3_3 65 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 124 241 (accept_3_3 62 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 124 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 124 241 (Polychromatic418967fa.accept_19_3_10_13_1_3482 60 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 124 241 (accept_3_3 59 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 124 241 (accept_3_3 56 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 124 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 55 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 124 241 (Polychromatic418967fa.accept_19_16_10_13_1_4922 54 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 241 (accept_3_3 53 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 124 241 (Polychromatic418967fa.accept_16_4_12_1_1_1204 52 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 124 241 (accept_3_3 50 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 124 241 (Polychromatic418967fa.accept_21_7_19_10_1_8567 49 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 124 241 (Polychromatic418967fa.accept_15_3_4_1_1_1072 48 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 241 (accept_3_3 47 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 124 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 124 241 (accept_3_3 44 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 124 241 (Polychromatic418967fa.accept_15_12_4_1_1_3746 42 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 241 (accept_3_3 41 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 40 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 241 (accept_3_3 38 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 241 (accept_3_3 35 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 241 (accept_3_3 32 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 241 (Polychromatic418967fa.accept_20_11_4_1_1_4389 31 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 241 (accept_3_3 29 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 241 (Polychromatic418967fa.accept_19_9_10_13_1_2291 28 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 241 (accept_3_3 26 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 241 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 241 (Polychromatic418967fa.accept_16_8_12_1_1_7720 24 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 241 (accept_3_3 23 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 241 (accept_3_3 20 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 241 (Polychromatic418967fa.accept_14_5_12_3_1_3397 19 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 241 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 241 (accept_3_3 17 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 241 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 124 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 241 (accept_3_3 14 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 241 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 241 (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 241 (accept_3_3 11 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 241 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 124
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 241 (accept_3_3 8 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 241 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 241 (Polychromatic418967fa.accept_17_6_5_3_1_7134 6 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 241 (accept_3_3 5 124 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 241 (Polychromatic418967fa.accept_16_4_12_1_1_1204 4 124 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 241
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 241 (accept_3_3 2 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 241 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 124 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  241))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 123 241 (Eq.refl Bool.true) (allA_succ_of_accept 118 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2
  118 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 123 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 117 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 123 241 (accept_3_3 116 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  115 123 241 (Polychromatic418967fa.accept_17_13_4_3_1_1446 115 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 114 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 241 (accept_3_3 113 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 112 123
  241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 123 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 111 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 123 241 (accept_3_3 110 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  109 123 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 109 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 123 241 (Polychromatic418967fa.accept_10_8_3_1_1_1316 108 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 241 (accept_3_3 107 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 106 123 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 123 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 105 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 123 241 (accept_3_3 104 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 123 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 103 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 241 (accept_3_3 101 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 123 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 99 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 123 241 (accept_3_3 98 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 123 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 97 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 123 241 (Polychromatic418967fa.accept_15_6_3_1_1_3678 96 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 241 (accept_3_3 95 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 94 123 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 123 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 93 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 123 241 (accept_3_3 92 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 123 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 91 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 241 (accept_3_3 89 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 241
  (Polychromatic418967fa.accept_13_9_6_7_1_551 87 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 123 241 (accept_3_3 86 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 123 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 123 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 241 (accept_3_3 83 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 123 241 (accept_3_3 80 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 123 241 (Polychromatic418967fa.accept_13_1_6_7_1_550 79 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 241 (accept_3_3 77 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 123 241 (accept_3_3 74 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 123 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 123 241 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 241 (accept_3_3 71 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 123 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 123 241 (accept_3_3 68 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 123 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 241 (accept_3_3 65 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 241
  (Polychromatic418967fa.accept_14_7_11_3_1_5365 63 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 123 241 (accept_3_3 62 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 123 241 (Polychromatic418967fa.accept_13_9_6_7_1_551 61 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 123 241 (Polychromatic418967fa.accept_16_12_11_1_1_4088 60 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 241 (accept_3_3 59 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 123 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 123 241 (accept_3_3 56 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 123 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 241 (accept_3_3 53 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 241
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 123 241 (accept_3_3 50 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 123 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 123 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 241 (accept_3_3 47 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 241
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 123 241 (accept_3_3 44 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 123 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 241 (accept_3_3 41 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 123 241 (accept_3_3 38 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 123 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 241 (accept_3_3 35 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 123 241 (accept_3_3 32 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 123 241 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 241 (accept_3_3 29 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 241
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 123 241 (accept_3_3 26 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 123 241 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 123 241 (Polychromatic418967fa.accept_17_7_4_3_1_3456 24 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 241 (accept_3_3 23 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 241
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 241 (accept_3_3 20 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 241 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 241 (accept_3_3 17 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 241
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 241 (accept_3_3 14 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 241 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 241 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 241 (accept_3_3 11 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 241
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 241 (accept_3_3 8 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 241 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 241 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 241 (accept_3_3 5 123 241 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 241 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 241 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 241
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 241 (accept_3_3 2 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 241 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 123 241 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123
  241)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_241_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


