-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch248
-- name    : Polychromatic418967fa_Branch248
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:48.166852+00:00
-- url     : https://prove2.me/theorems/20366749-5d1e-499d-a92f-1167d40ca729
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch248_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_248 : allB 248 248 :=
  allB_succ' 2 247 248 (Eq.refl Bool.true) (allA_of_3_0 2 247 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  246 248 (Eq.refl Bool.true) (allA_succ_of_gcd 2 246 248 2 1 123 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 248 (accept_3_2 1 246 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 246 248))) (allB_succ' 4 245 248 (Eq.refl Bool.true) (allA_succ_of_accept 3 245 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 245 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 245 248 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 245 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 248 (accept_3_2 1 245 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 245 248)))) (allB_succ' 5 244 248 (Eq.refl Bool.true) (allA_of_3_0 5 244 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 243 248 (Eq.refl Bool.true) (allA_succ_of_accept 5 243 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 243 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 243 248 (accept_3_2 4 243 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  243 248 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 243 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 243 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 243 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 248 (accept_3_2 1 243 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 243 248)))))) (allB_succ' 7 242 248 (Eq.refl Bool.true) (allA_succ_of_gcd 6 242 248 2 3
  121 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 242 248
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 242 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 242 248 2 2 121 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 242 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 242 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 242 248 2 1 121 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 242 248 (accept_3_2 1 242 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 242 248))))))) (allB_succ' 8 241 248 (Eq.refl Bool.true) (allA_of_3_0 8 241
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 240 248 (Eq.refl Bool.true) (allA_succ_of_gcd 8 240 248 8 1
  30 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 248
  (accept_3_2 7 240 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 248 2 3 120 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 248
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 240 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 240 248 4 1 60 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 240 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 240 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 240 248 2 1 120 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 248 (accept_3_2 1 240 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 240 248))))))))) (allB_succ' 10 239 248 (Eq.refl Bool.true) (allA_succ_of_accept 9 239
  248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 239 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 239 248 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 239 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 248 (accept_3_2 7 239 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 239 248 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 239 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  239 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 248 (accept_3_2 4 239
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 248 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 239 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 239 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 248 (accept_3_2 1 239 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  248)))))))))) (allB_succ' 11 238 248 (Eq.refl Bool.true) (allA_of_3_0 11 238 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 237 248 (Eq.refl Bool.true) (allA_succ_of_accept 11 237 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 237 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 248 (accept_3_2 10 237 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  237 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 237 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 237 248 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 237 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 248 (accept_3_2 7 237 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 237 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 248 (accept_3_2 4 237 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  237 248 (Polychromatic418967fa.accept_14_3_13_10_1_761 3 237 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 237 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 237 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 248 (accept_3_2 1 237 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 237 248)))))))))))) (allB_succ' 13 236 248 (Eq.refl Bool.true) (allA_succ_of_gcd 12 236
  248 4 3 59 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  236 248 (Polychromatic418967fa.accept_16_11_12_8_1_1592 11 236 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 236 248 2 5 118 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 236 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 236 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 236 248 4 2 59 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 236 248 (accept_3_2 7 236 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236 248 2 3 118 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 248 (Polychromatic418967fa.accept_14_5_12_10_1_2985
  5 236 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 248 4 1 59 62 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 236 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 248 2 1 118 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 248 (accept_3_2 1 236 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  248))))))))))))) (allB_succ' 14 235 248 (Eq.refl Bool.true) (allA_of_3_0 14 235 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 234 248 (Eq.refl Bool.true) (allA_succ_of_gcd 14 234 248 2 7 117 124 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 248 (accept_3_2 13 234 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 234 248 2 6 117 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 248
  (Polychromatic418967fa.accept_19_11_6_1_1_2826 11 234 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 234 248 2 5 117 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 234 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 234 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 248 2 4 117 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 248 (accept_3_2 7 234 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 248 2 3 117 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 248 (Polychromatic418967fa.accept_17_5_13_10_1_3949
  5 234 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 248 2 2 117 124
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 234 248
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 234 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 234 248 2 1 117 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 234 248 (accept_3_2 1 234 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  248))))))))))))))) (allB_succ' 16 233 248 (Eq.refl Bool.true) (allA_succ_of_accept 15 233 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 233 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 233 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 233 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 248 (accept_3_2 13 233 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 233 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 233 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 248 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 233 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 248 (accept_3_2 10
  233 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 233 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 233 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 248 (accept_3_2 7 233 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 233 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 233 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 5
  233 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 248 (accept_3_2 4 233
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 248 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 233 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 248
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 233 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 248 (accept_3_2 1 233 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  248)))))))))))))))) (allB_succ' 17 232 248 (Eq.refl Bool.true) (allA_of_3_0 17 232 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 231 248 (Eq.refl Bool.true) (allA_succ_of_accept 17 231 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 231 248 (accept_3_2 16 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 231 248 (Polychromatic418967fa.accept_16_15_7_8_1_8189 15 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 231 248 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 231 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 248 (accept_3_2 13 231 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 231 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 231 248 (accept_3_2 10 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  231 248 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 231 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 231 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 248 (accept_3_2 7 231 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 231 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 248 (accept_3_2 4 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  231 248 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 231 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 231 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 231 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 248 (accept_3_2 1 231 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 231 248)))))))))))))))))) (allB_succ' 19 230 248 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 230 248 2 9 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 230 248 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 230 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 248 2 8 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 248 (Polychromatic418967fa.accept_13_2_9_1_1_67 15
  230 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 230 248 2 7 115 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 230 248 (accept_3_2 13
  230 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 230 248 2 6 115 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 230 248
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 230 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 230 248 2 5 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 230 248 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 230 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 230 248 2 4 115 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 230 248 (accept_3_2 7 230 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 230 248 2 3 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 230 248 (Polychromatic418967fa.accept_11_5_10_6_1_793 5
  230 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 248 2 2 115 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 248
  (Polychromatic418967fa.accept_14_3_6_10_1_752 3 230 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 248 2 1 115 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 248 (accept_3_2 1 230 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  248))))))))))))))))))) (allB_succ' 20 229 248 (Eq.refl Bool.true) (allA_of_3_0 20 229 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 228 248 (Eq.refl Bool.true) (allA_succ_of_gcd 20 228 248 4 5 57 62 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 248 (accept_3_2 19 228 248
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 248 2 9 114 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 248
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 228 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 228 248 4 4 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 228 248 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 228 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 248 2 7 114 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 248 (accept_3_2 13 228 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 248 4 3 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 228 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 248 2 5 114 124 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 248
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 228 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 228 248 4 2 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 228 248 (accept_3_2 7 228 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228
  248 2 3 114 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  228 248 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 228 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 228 248 4 1 57 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 228 248 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 228 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 248 2 1 114 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 248 (accept_3_2 1 228 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 228 248))))))))))))))))))))) (allB_succ' 22 227 248 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 227 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 248 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 227
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 248 (accept_3_2 19 227
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 248
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 227 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 227 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 248 (accept_3_2 16 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 227 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 248 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 227 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 248 (accept_3_2 13
  227 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 248
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 227 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 227 248 (Polychromatic418967fa.accept_16_11_3_8_1_4597 11 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 248 (accept_3_2 10 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 227 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 227 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 248 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  227 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 248 (accept_3_2 7 227
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 248
  (Polychromatic418967fa.accept_9_6_2_5_1_506 6 227 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 227 248 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 248 (accept_3_2 4 227 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 227 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 248 (Polychromatic418967fa.accept_12_2_11_8_1_504
  2 227 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 248 (accept_3_2 1
  227 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227 248)))))))))))))))))))))) (allB_succ' 23 226 248
  (Eq.refl Bool.true) (allA_of_3_0 23 226 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 225 248 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 225 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 248 (accept_3_2 22 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 248 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 225 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 248
  (Polychromatic418967fa.accept_16_4_1_8_1_835 20 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 248 (accept_3_2 19 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 248 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 248 (accept_3_2 16 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 248 (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 225 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 248
  (Polychromatic418967fa.accept_20_14_5_8_1_4870 14 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 248 (accept_3_2 13 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 248 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 248 (accept_3_2 10 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 248 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 225 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 248
  (Polychromatic418967fa.accept_19_8_16_1_1_11051 8 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 248 (accept_3_2 7 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 248 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 248 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 248 (accept_3_2 4 225 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 248 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 225 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 248
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 248 (accept_3_2 1 225 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  248)))))))))))))))))))))))) (allB_succ' 25 224 248 (Eq.refl Bool.true) (allA_succ_of_gcd 24 224 248 8 3 28 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 224 248
  (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 224 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 224 248 2 11 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 224 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 224 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 224 248 4 5 56 62 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 224 248 (accept_3_2 19 224 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 224 248 2 9 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 224 248 (Polychromatic418967fa.accept_13_4_3_1_1_2898
  17 224 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 248 8 2 28 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 248
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 224 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 248 2 7 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 248 (accept_3_2 13 224 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 248 4 3 56 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 224 248 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 224 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 248 2 5 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 248 (Polychromatic418967fa.accept_10_9_4_8_1_741 9
  224 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 248 8 1 28 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 224 248 (accept_3_2 7
  224 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224 248 2 3 112 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 248
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 224 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 224 248 4 1 56 62 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 224 248 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 224 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 248 2 1 112 124 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 248 (accept_3_2 1 224 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 248))))))))))))))))))))))))) (allB_succ' 26 223 248 (Eq.refl Bool.true)
  (allA_of_3_0 26 223 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 222 248 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 222 248 2 13 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 222 248 (accept_3_2 25 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 248 2 12 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 248 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 222 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 248 2 11 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 222 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 222 248 2 10 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 222 248 (accept_3_2 19 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 248 2 9 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 248 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 222 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 248 2 8 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 222 248
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 222 248 2 7 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 248 (accept_3_2 13 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 248 2 6 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 248 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 222 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 248 2 5 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 222 248
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 222 248 2 4 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 222 248 (accept_3_2 7 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 248 2 3 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 248 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 222 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 248 2 2 111 124 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 248
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 248 2 1 111 124 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 248 (accept_3_2 1 222 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  248))))))))))))))))))))))))))) (allB_succ' 28 221 248 (Eq.refl Bool.true) (allA_succ_of_accept 27 221 248
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 221 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 221 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 248 (accept_3_2 25 221 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 221 248 (Polychromatic418967fa.accept_19_5_12_1_1_2817 24 221 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 248
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 221 248 (accept_3_2 22 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 221 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 248 (accept_3_2 19 221 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 248 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 221 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 248
  (Polychromatic418967fa.accept_22_17_1_6_1_15031 17 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 221 248 (accept_3_2 16 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 221 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 221 248 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 248 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 221
  248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 248 (accept_3_2 13 221
  248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 248
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 12 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 248 (Polychromatic418967fa.accept_16_11_13_8_1_1578 11 221 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 248 (accept_3_2 10 221 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 248
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 248 (accept_3_2 7 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 248 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 248 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 221 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 248 (accept_3_2 4 221 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 248 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 221 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 248
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 248 (accept_3_2 1 221 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  248)))))))))))))))))))))))))))) (allB_succ' 29 220 248 (Eq.refl Bool.true) (allA_of_3_0 29 220 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 219 248 (Eq.refl Bool.true) (allA_succ_of_accept 29 219 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 248 (accept_3_2 28 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 219 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 219 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 248 (accept_3_2 25 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 248 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 219 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 248 (accept_3_2 22 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 219 248 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 219 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 248 (accept_3_2 19 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 248 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 219 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 248 (accept_3_2 16 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 248 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 219 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 248 (accept_3_2 13 219 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 248 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 219 248
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 248 (accept_3_2 10 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 248 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 248 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 248 (accept_3_2 7 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 248 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 219 248 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 248
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 248 (accept_3_2 4 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 248 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 219 248 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 248 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 248 (accept_3_2 1 219 248 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 248))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_248_segment_001)))))))))))))))))))))))))))))


