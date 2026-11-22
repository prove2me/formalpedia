-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch235
-- name    : Polychromatic418967fa_Branch235
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:23.738091+00:00
-- url     : https://prove2.me/theorems/76100a14-ba46-44bb-9b9a-9dcaa02d0d07
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch235_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_235 : allB 235 235 :=
  allB_succ' 2 234 235 (Eq.refl Bool.true) (allA_succ_of_accept 1 234 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  234 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234 235)) (allB_succ' 3 233 235
  (Eq.refl Bool.true) (allA_of_3_1 3 233 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 232 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 232 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 235 (accept_3_3 2 232 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 232 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 232 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 235)))) (allB_succ' 5 231 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 231 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 231 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 235 (accept_3_3 2 231 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  231 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 235))))) (allB_succ' 6 230 235
  (Eq.refl Bool.true) (allA_of_3_1 6 230 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 229 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 229 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 229 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 235 (accept_3_3 5 229 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 229 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 229 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 235 (accept_3_3 2 229 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 229 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 235))))))) (allB_succ' 8 228 235 (Eq.refl Bool.true) (allA_succ_of_accept 7 228 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 228 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 228 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 228 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 235 (accept_3_3 5 228 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 228 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 228 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 3
  228 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 235 (accept_3_3 2 228
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 235
  (Polychromatic418967fa.accept_11_1_8_4_1_717 1 228 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 235)))))))) (allB_succ' 9 227 235 (Eq.refl Bool.true) (allA_of_3_1 9 227 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 226 235 (Eq.refl Bool.true) (allA_succ_of_accept 9 226 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 226 235 (accept_3_3 8 226 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  226 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 226 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 226 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 226 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 226 235 (accept_3_3 5 226 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 226 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 226 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 226 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 226 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 226 235 (accept_3_3 2 226 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  226 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 226 235)))))))))) (allB_succ' 11 225 235 (Eq.refl Bool.true) (allA_succ_of_gcd 10 225 235 5 2 45
  47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 225 235
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 225 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 225 235 (accept_3_3 8 225 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  225 235 (Polychromatic418967fa.accept_17_7_4_14_1_2106 7 225 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 225 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 225 235 5 1 45 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  225 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 225 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 225 235 (accept_3_3 2 225 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  225 235 (Polychromatic418967fa.accept_17_1_4_14_1_8058 1 225 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 225 235))))))))))) (allB_succ' 12 224 235 (Eq.refl Bool.true) (allA_of_3_1 12 224 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 223 235 (Eq.refl Bool.true) (allA_succ_of_accept 12 223 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 223 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 235 (accept_3_3 11 223 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 223 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 223 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 235 (accept_3_3 8 223 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 223 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 223 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 235 (accept_3_3 5 223 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 223 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 223 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 235 (accept_3_3 2 223 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 223 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 235))))))))))))) (allB_succ' 14 222 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 222 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  222 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 222 235 (accept_3_3 11
  222 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 235
  (Polychromatic418967fa.accept_17_10_1_14_1_489 10 222 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 222 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 235 (accept_3_3 8 222 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 222 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 222 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  222 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 235 (accept_3_3 5 222
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 222 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 222 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 222 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 235 (accept_3_3 2 222 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 222 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 235)))))))))))))) (allB_succ' 15 221 235 (Eq.refl Bool.true)
  (allA_of_3_1 15 221 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 220 235 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 220 235 5 3 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 220 235 (accept_3_3 14 220 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 220 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 220 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 220 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 220 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 220 235 (accept_3_3 11 220 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 220 235 5 2 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 235 (accept_3_3 8 220 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 220 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  220 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 220 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 220 235 5 1 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 220 235 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 220 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 235 (accept_3_3 2 220 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  220 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 235)))))))))))))))) (allB_succ' 17
  219 235 (Eq.refl Bool.true) (allA_succ_of_accept 16 219 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 219 235 (accept_3_3 14 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 219 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 219 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 219 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 235 (accept_3_3 11 219 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 219 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 219 235 (accept_3_3 8 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  219 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 219 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 219 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 235 (accept_3_3 5 219 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 235
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 219 235 (accept_3_3 2 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  219 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 219 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 219 235))))))))))))))))) (allB_succ' 18 218 235 (Eq.refl Bool.true) (allA_of_3_1 18 218 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 217 235 (Eq.refl Bool.true) (allA_succ_of_accept 18 217 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 235 (accept_3_3 17 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 217 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 235 (accept_3_3 14 217 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 217 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 235
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 235 (accept_3_3 11 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 235 (Polychromatic418967fa.accept_19_9_8_7_1_2061 9 217 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 235 (accept_3_3 8 217 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 217 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 235 (accept_3_3 5 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 235 (Polychromatic418967fa.accept_14_4_7_11_1_790 4 217 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 217 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 235 (accept_3_3 2 217 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 217 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 235))))))))))))))))))) (allB_succ' 20 216 235
  (Eq.refl Bool.true) (allA_succ_of_accept 19 216 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 216 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 235
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 216 235 (accept_3_3 17 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 216 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 216 235 (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 216 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 235 (accept_3_3 14 216 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 235 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 216
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 216 235 (accept_3_3 11 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 216 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 216 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 216 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 235 (accept_3_3 8 216 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 235 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 216 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 235
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 216 235 (accept_3_3 5 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  216 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 216 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 216 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 216 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 235 (accept_3_3 2 216 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 216 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 235)))))))))))))))))))) (allB_succ' 21 215 235
  (Eq.refl Bool.true) (allA_of_3_1 21 215 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 214 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 235 (accept_3_3 20 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 214 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 235
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 235 (accept_3_3 17 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 235 (accept_3_3 14 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 214 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 235 (accept_3_3 11 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 235 (accept_3_3 8 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 214 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 235 (accept_3_3 5 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 214 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 235 (accept_3_3 2 214 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214 235)))))))))))))))))))))) (allB_succ' 23 213 235
  (Eq.refl Bool.true) (allA_succ_of_accept 22 213 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 213 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 213 235 (accept_3_3 20 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 213 235 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 213 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 235 (accept_3_3 17 213 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 213 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 213 235 (accept_3_3 14 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 213 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 213 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 213 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 235 (accept_3_3 11 213 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 235
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 213 235 (accept_3_3 8 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  213 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 213 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 235 (accept_3_3 5 213 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 235 (accept_3_3 2 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 213 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 235))))))))))))))))))))))) (allB_succ' 24 212 235 (Eq.refl Bool.true) (allA_of_3_1 24 212
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 211 235 (Eq.refl Bool.true) (allA_succ_of_accept 24 211
  235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 211 235 (accept_3_3 23 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 211 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 211 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 211 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 235 (accept_3_3 20 211 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 235 (Polychromatic418967fa.accept_7_5_1_4_1_122
  19 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 235
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 235 (accept_3_3 17 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 211 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 235 (accept_3_3 14 211 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 211 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 235 (accept_3_3 11 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 211 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 235 (accept_3_3 8 211 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 211 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 235 (accept_3_3 5 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 211 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 211 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 235 (accept_3_3 2 211 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 235 (Polychromatic418967fa.accept_19_1_2_7_1_2054 1 211 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 235))))))))))))))))))))))))) (allB_succ' 26 210 235
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 210 235 5 5 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 210 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 210 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 235 (accept_3_3 23 210 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 210 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 210 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 235 5 4 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 210 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 210 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 235 (Polychromatic418967fa.accept_19_18_1_7_1_14104 18 210
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 235 (accept_3_3 17 210
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 16 210 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 210 235 5 3 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 210 235 (accept_3_3 14 210 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 210 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 210 235 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 210 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 235 (accept_3_3 11 210 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 235 5 2 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 235 (accept_3_3 8 210 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  210 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 210 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 210 235 5 1 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 210 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 210 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 210 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 235 (accept_3_3 2 210 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  210 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 235))))))))))))))))))))))))))
  (allB_succ' 27 209 235 (Eq.refl Bool.true) (allA_of_3_1 27 209 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 28 208 235 (Eq.refl Bool.true) (allA_succ_of_accept 27 208 235 (Polychromatic418967fa.accept_6_3_4_1_1_8
  27 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 208 235 (accept_3_3 26
  208 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 208 235
  (Polychromatic418967fa.accept_19_6_18_7_1_10032 25 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 235 (Polychromatic418967fa.accept_17_7_4_14_1_2106 24 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 235 (accept_3_3 23 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 208 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 235 (accept_3_3 20 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 235 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 235 (accept_3_3 17 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 208 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 208 235 (accept_3_3 14 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 208 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 208 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 235 (accept_3_3 11 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 208
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 208 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 208 235 (accept_3_3 8 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  208 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 208 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 208 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 235 (accept_3_3 5 208 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 208 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 208 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 208 235 (accept_3_3 2 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  208 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 208 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 208 235)))))))))))))))))))))))))))) (allB_succ' 29 207 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 207 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 207 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 235 (Polychromatic418967fa.accept_21_6_18_4_1_4952 27 207
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 235 (accept_3_3 26 207
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 235
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 25 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 207 235 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 207 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 235 (accept_3_3 23 207 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 207 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 207 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 235 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 235 (accept_3_3 20
  207 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 235
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 207 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 207 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 235 (accept_3_3 17 207 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 235
  (Polychromatic418967fa.accept_13_2_12_1_1_343 15 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 207 235 (accept_3_3 14 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 207 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 207 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 235 (accept_3_3 11 207 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 207 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 235 (accept_3_3 8 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 207 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 235 (accept_3_3 5 207 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 235 (accept_3_3 2 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 235 (Polychromatic418967fa.accept_16_1_15_11_1_356 1 207 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 235))))))))))))))))))))))))))))) (allB_succ' 30 206 235 (Eq.refl Bool.true) (allA_of_3_1 30
  206 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 205 235 (Eq.refl Bool.true) (allA_succ_of_gcd 30 205
  235 5 6 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  205 235 (accept_3_3 29 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 235
  (Polychromatic418967fa.accept_20_8_5_15_1_9868 28 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 205 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 205 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 235 (accept_3_3 26 205 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 205 235 5 5 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 205 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 205 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 235 (accept_3_3 23 205 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 205 235 5 4 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 205 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 205 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 235 (accept_3_3 17 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 235
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 205 235 5 3 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 205 235 (accept_3_3 14 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 205 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 235 (accept_3_3 11 205 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 205 235 5 2 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 205 235 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 235 (accept_3_3 8 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 235 (Polychromatic418967fa.accept_20_7_5_15_1_1548
  7 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 205 235 5 1 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 205 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 205 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 235 (accept_3_3 2 205 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 235 (Polychromatic418967fa.accept_20_1_5_15_1_6913
  1 205 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  235))))))))))))))))))))))))))))))) (allB_succ' 32 204 235 (Eq.refl Bool.true) (allA_succ_of_accept 31 204 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 204 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 204 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 204 235 (accept_3_3 29 204 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 204 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 204 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 204 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 204 235 (accept_3_3 26 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 204 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 204 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 204 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 204 235 (accept_3_3 23 204 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 235 (Polychromatic418967fa.accept_9_4_6_1_1_393
  22 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 204 235 (accept_3_3 20 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 204 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 204 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 204 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 204 235 (accept_3_3 17 204 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 204 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 204 235 (accept_3_3 14 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 204 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 204 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 204 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 235 (accept_3_3 11 204 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 204 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 235
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 204 235 (accept_3_3 8 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  204 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 204 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 204 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 235 (accept_3_3 5 204 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 204 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 204 235 (accept_3_3 2 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  204 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 204 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 204 235)))))))))))))))))))))))))))))))) (allB_succ' 33 203 235 (Eq.refl Bool.true) (allA_of_3_1
  33 203 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 202 235 (Eq.refl Bool.true) (allA_succ_of_accept 33
  202 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 202 235 (accept_3_3 32 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 202 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 202 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 202 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 202 235 (accept_3_3 29 202 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 202 235 (Polychromatic418967fa.accept_10_8_2_5_1_596
  28 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 202 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 202 235 (accept_3_3 26 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 202 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 202 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 202 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 202 235 (accept_3_3 23 202 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 202 235 (Polychromatic418967fa.accept_19_3_12_7_1_10004 22 202 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 202 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 202 235 (accept_3_3 20 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 202 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 202 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 202 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 202 235 (accept_3_3 17 202 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 202 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 202 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 202 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 202 235 (accept_3_3 14 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 202 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 202 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 202 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 202 235 (accept_3_3 11 202 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 202 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 202 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 202 235 (accept_3_3 8 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  202 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 202 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 202 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 202 235 (accept_3_3 5 202 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 202 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 202 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 202 235 (accept_3_3 2 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  202 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 202 235)))))))))))))))))))))))))))))))))) (allB_succ' 35 201 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 201 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 201 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 201 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 235 (accept_3_3 32 201 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 235 (Polychromatic418967fa.accept_9_4_3_1_1_154
  31 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 235 (accept_3_3 29 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 201 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 201 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 235 (accept_3_3 26 201 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 201 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 235 (accept_3_3 23 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 201 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 235 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 201 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 235 (accept_3_3 20 201 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 201
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 201 235 (accept_3_3 17 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 201 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 201 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 201 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 235 (accept_3_3 14 201 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 201 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 235
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 235 (accept_3_3 11 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 235 (accept_3_3 8 201 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 235 (accept_3_3 5 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 201 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 235 (accept_3_3 2 201 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 201 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 235))))))))))))))))))))))))))))))))))) (allB_succ'
  36 200 235 (Eq.refl Bool.true) (allA_of_3_1 36 200 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 199 235
  (Eq.refl Bool.true) (allA_succ_of_accept 36 199 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 235 (accept_3_3 35 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 199 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 235
  (Polychromatic418967fa.accept_22_11_1_15_1_11044 33 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 199 235 (accept_3_3 32 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 199 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 199 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 199
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 235 (accept_3_3 29 199
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 199 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 199 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 235 (accept_3_3 26 199 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 199 235 (Polychromatic418967fa.accept_20_5_19_15_1_3946 25 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 235
  (Polychromatic418967fa.accept_10_4_9_5_1_84 24 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 235 (accept_3_3 23 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 199 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 235 (accept_3_3 20 199 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 235
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 235 (accept_3_3 17 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 199 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 235 (accept_3_3 14 199 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 235 (accept_3_3 11 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 235 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 235 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 235 (accept_3_3 8 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 199
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 235 (accept_3_3 5 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 199 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 235 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 199 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 235 (accept_3_3 2 199 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 199 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 235))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 198 235 (Eq.refl Bool.true) (allA_succ_of_accept 37 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 198 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 198 235 (accept_3_3 35 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 198 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 235 (accept_3_3 32 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 235
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 198 235 (accept_3_3 29 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 198 235 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 198 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 235 (accept_3_3 26 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 235
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 198 235 (accept_3_3 23 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 198 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 235 (accept_3_3 20 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 235
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 235 (accept_3_3 17 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 235 (Polychromatic418967fa.accept_17_16_11_14_1_4213 16 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 198 235 (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 235 (accept_3_3 14 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 198 235 (accept_3_3 11 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 198 235 (Polychromatic418967fa.accept_20_10_18_15_1_5359 10 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 235 (accept_3_3 8 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 198 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 235 (accept_3_3 5 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 235 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 198 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 235 (accept_3_3 2 198 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 235))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 197 235 (Eq.refl Bool.true) (allA_of_3_1 39 197 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 196 235 (Eq.refl Bool.true) (allA_succ_of_accept 39 196 235 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 196 235 (accept_3_3 38
  196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 196 235
  (Polychromatic418967fa.accept_15_7_1_10_1_305 37 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 196 235 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 196 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 196 235 (accept_3_3 35 196 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 196 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 235 (accept_3_3 32
  196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 196 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 196 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 196 235 (accept_3_3 29 196 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 196 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 196 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 196 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 196 235 (accept_3_3 26 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 196 235 (Polychromatic418967fa.accept_16_9_4_11_1_2661 25 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 196 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 196 235 (accept_3_3 23 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 196 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 196 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 196 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 196 235 (accept_3_3 20 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 196 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 196 235 (Polychromatic418967fa.accept_19_18_6_7_1_5882 18 196 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 235 (accept_3_3 17 196 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 235 (Polychromatic418967fa.accept_19_16_6_7_1_4425 16 196
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 196 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 196 235 (accept_3_3 14 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 196 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 196 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 235 (accept_3_3 11 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 196 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 196 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 196 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 196 235 (accept_3_3 8 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  196 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 196 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 235 (accept_3_3 5 196 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 196 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 196 235 (accept_3_3 2 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  196 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 196 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 196 235)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 195 235 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 195 235 5 8 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 195 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 195 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 235 (accept_3_3 38 195 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 195 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 195 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 235
  (Polychromatic418967fa.accept_19_17_5_7_1_5896 36 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 195 235 5 7 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 195 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 195 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 235 (accept_3_3 32 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 235 5 6 39 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 235 (accept_3_3 29
  195 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 195 235 (Polychromatic418967fa.accept_30_27_15_25_1_14122 27 195 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 235 (accept_3_3 26 195 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 195 235 5 5 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 195 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 235 (accept_3_3 23 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 195 235 5 4 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 195 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 195 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 195
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 235 (accept_3_3 17 195
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 195 235 5 3 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 195 235 (accept_3_3 14 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 195 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 195 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 235 (accept_3_3 11 195 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 195 235 5 2 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 195 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 235 (accept_3_3 8 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7
  195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 235
  (Polychromatic418967fa.accept_16_6_3_11_1_3751 6 195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 195 235 5 1 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 195 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 235 (accept_3_3 2 195 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 1
  195 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  235))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 194 235 (Eq.refl Bool.true) (allA_of_3_1 42 194 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 193 235 (Eq.refl Bool.true) (allA_succ_of_accept 42 193 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 235 (accept_3_3 41 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 235 (Polychromatic418967fa.accept_24_16_1_19_1_14121 40 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 235 (accept_3_3 38 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 193
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 235
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 193 235 (accept_3_3 35 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 193 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 193 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 193 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 235 (accept_3_3 32 193 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 235
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 193 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 235 (accept_3_3 29 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 235 (accept_3_3 26 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 235 (accept_3_3 23 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 235 (accept_3_3 20 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 235 (accept_3_3 17 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 235 (accept_3_3 14 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 235 (Polychromatic418967fa.accept_11_2_6_4_1_3028 13 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 235 (accept_3_3 11 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 235
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 235 (accept_3_3 8 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 235 (accept_3_3 5 193 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 193 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 235 (accept_3_3 2 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 193 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 235))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 192 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 192 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 192 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 192 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 192 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 192 235 (accept_3_3 41 192 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 235 (Polychromatic418967fa.accept_9_4_3_1_1_154
  40 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 235
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 192 235 (accept_3_3 38 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 192 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 192 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 192 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 235 (accept_3_3 35 192 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 192 235 (accept_3_3 32 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 192 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 192 235 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 192 235 (accept_3_3 29 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 192
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 192 235 (accept_3_3 26 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 192 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 192 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 192 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 235 (accept_3_3 23 192 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 192 235 (accept_3_3 20 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 192 235 (Polychromatic418967fa.accept_17_2_5_14_1_2068 19 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 192 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 235 (accept_3_3 17 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 192 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 192 235 (accept_3_3 14 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 192 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 192 235 (Polychromatic418967fa.accept_21_12_3_4_1_4988 12 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 235 (accept_3_3 11 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 192
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 235
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 192 235 (accept_3_3 8 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  192 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 192 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 192 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 235 (accept_3_3 5 192 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 192 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 235
  (Polychromatic418967fa.accept_10_3_2_5_1_295 3 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 192 235 (accept_3_3 2 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  192 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 192 235)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 191 235 (Eq.refl Bool.true)
  (allA_of_3_1 45 191 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 190 235 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 190 235 5 9 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 190 235 (accept_3_3 44 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 190 235 (Polychromatic418967fa.accept_20_3_10_15_1_620 43 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 190 235 (Polychromatic418967fa.accept_20_2_10_15_1_3953 42 190 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 190 235 (accept_3_3 41 190 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 190 235 5 8 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 190 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39
  190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 190 235 (accept_3_3 38
  190 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 190 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 190 235 (Polychromatic418967fa.accept_17_2_3_14_1_8043 36 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 190 235 5 7 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 190 235
  (Polychromatic418967fa.accept_18_16_10_1_1_3696 34 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 190 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 190 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 190 235 (accept_3_3 32 190 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 190 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 190 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 190 235 5 6 38 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 235 (accept_3_3 29 190 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 190 235 (Polychromatic418967fa.accept_12_4_10_7_1_149
  28 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 190 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 190 235 (accept_3_3 26 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  190 235 5 5 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 190 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 190 235 (accept_3_3 23 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 190 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 190 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 190 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 235 5 4 38 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 190 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 190 235 (accept_3_3 17 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 190 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 190 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 190 235 5 3 38 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 190 235 (accept_3_3 14 190 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13
  190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 235 (accept_3_3 11 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  190 235 5 2 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 190 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 190 235 (accept_3_3 8 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 190 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 235 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 190 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 190 235 5 1 38 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 190 235
  (Polychromatic418967fa.accept_12_4_10_7_1_149 4 190 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 190 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 235 (accept_3_3 2 190 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 190 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 235)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  47 189 235 (Eq.refl Bool.true) (allA_succ_of_accept 46 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 189 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 235
  (Polychromatic418967fa.accept_13_6_7_1_1_335 45 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 189 235 (accept_3_3 44 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 189 235 (Polychromatic418967fa.accept_20_3_9_15_1_6847 43 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 235 (accept_3_3 41 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 189 235 (accept_3_3 38 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 189 235 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 235 (accept_3_3 35 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 189 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 189 235 (accept_3_3 32 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 189 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 235 (accept_3_3 29 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 189 235 (accept_3_3 26 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 189 235 (Polychromatic418967fa.accept_19_6_18_7_1_10032 25 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 189 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 235 (accept_3_3 23 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 235
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 235 (accept_3_3 20 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 235 (Polychromatic418967fa.accept_13_6_7_1_1_335 19 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 235 (accept_3_3 17 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 235 (accept_3_3 14 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 235 (Polychromatic418967fa.accept_25_13_14_10_1_5050 13 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 189 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 235 (accept_3_3 11 189 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 235
  (Polychromatic418967fa.accept_11_9_2_4_1_707 9 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 235 (accept_3_3 8 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 235 (Polychromatic418967fa.accept_22_7_13_15_1_9473 7 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 235 (accept_3_3 5 189 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 235 (accept_3_3 2 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 189 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 235))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 188 235 (Eq.refl
  Bool.true) (allA_of_3_1 48 188 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 187 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 187 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 187 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 187 235 (accept_3_3 47 187 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 187 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 46 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 235
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 187 235 (accept_3_3 44 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 187 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 187 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 235 (accept_3_3 41 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 187 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 235 (accept_3_3 38 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 235 (accept_3_3 35 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 187 235 (accept_3_3 32 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 187 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 235 (accept_3_3 29 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 235 (accept_3_3 26 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 235 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 235 (accept_3_3 23 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 235 (accept_3_3 20 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 235 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 235 (accept_3_3 17 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 187 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 235 (accept_3_3 14 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 235 (accept_3_3 11 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 235 (Polychromatic418967fa.accept_19_10_16_7_1_10039 10 187 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 235 (accept_3_3 8 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 235 (Polychromatic418967fa.accept_21_7_19_4_1_4956 7 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 235 (accept_3_3 5 187 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 187 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 235 (accept_3_3 2 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 187 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 235))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 186 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 186 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 48
  186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 186 235 (accept_3_3 47
  186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 235
  (Polychromatic418967fa.accept_15_1_6_10_1_23 46 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 186 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 235 (accept_3_3 44 186 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 186 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 235 (Polychromatic418967fa.accept_13_3_4_1_1_363
  42 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 186 235 (accept_3_3 41
  186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 40 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 186 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 186 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 235 (accept_3_3 38 186 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 235
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 186 235 (accept_3_3 35 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 186 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 235 (accept_3_3 32 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 186 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 186 235 (accept_3_3 29 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 186 235 (Polychromatic418967fa.accept_16_12_10_11_1_2667 28 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 186 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 235 (accept_3_3 26 186 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 235
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 186 235 (accept_3_3 23 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 186 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 235 (accept_3_3 20 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 186 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 235
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 186 235 (accept_3_3 17 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 186 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 186 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 186 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 235 (accept_3_3 14 186 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 235 (accept_3_3 11 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 235 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 235 (accept_3_3 8 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 186 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 235
  (Polychromatic418967fa.accept_21_6_18_4_1_4952 6 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 235 (accept_3_3 5 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 186 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 235 (accept_3_3 2 186 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  235)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 185 235 (Eq.refl Bool.true) (allA_of_3_1 51 185
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 184 235 (Eq.refl Bool.true) (allA_succ_of_accept 51 184
  235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 184 235 (accept_3_3 50 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 184 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 184 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 184 235 (accept_3_3 47 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 184 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 184 235 (accept_3_3 44 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 184 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 184 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 184 235 (accept_3_3 41 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 184 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 184 235 (accept_3_3 38 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 184 235 (Polychromatic418967fa.accept_14_9_2_11_1_780 37 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 184 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 184 235 (accept_3_3 35 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 184 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 184 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 184 235 (accept_3_3 32 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 184 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 184 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 184 235 (accept_3_3 29 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 184 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 184 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 184 235 (accept_3_3 26 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 184 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 184 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 235 (accept_3_3 23 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 184 235 (accept_3_3 20 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 184 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 184 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 235 (accept_3_3 17 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 184 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 235 (accept_3_3 14 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 235 (accept_3_3 11 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 235 (accept_3_3 8 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 235 (accept_3_3 5 184 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 235 (Polychromatic418967fa.accept_16_4_8_11_1_5961 4 184 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 235 (accept_3_3 2 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 184 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 235)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 183 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 235 (Polychromatic418967fa.accept_9_6_3_1_1_155
  51 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 235 (accept_3_3 50
  183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 183 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 183 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 235 (accept_3_3 47 183 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 235 (Polychromatic418967fa.accept_7_3_1_4_1_121
  45 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 235 (accept_3_3 44
  183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 43 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 183 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 183 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 235 (accept_3_3 41 183 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 235
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 183 235 (accept_3_3 38 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 183 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 183 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 235 (accept_3_3 35 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 235 (accept_3_3 32 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 235 (accept_3_3 29 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 235 (accept_3_3 26 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 183 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 235 (accept_3_3 23 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 235 (accept_3_3 20 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 235 (accept_3_3 17 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 235 (accept_3_3 14 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 235 (accept_3_3 11 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 235 (accept_3_3 8 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 235 (accept_3_3 5 183 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 235 (accept_3_3 2 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 235 (Polychromatic418967fa.accept_17_1_13_14_1_478 1 183 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 235))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 182 235 (Eq.refl
  Bool.true) (allA_of_3_1 54 182 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 181 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 181 235 (accept_3_3 53 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 181 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 181 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 181 235 (accept_3_3 50
  181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 181 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 49 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 181 235 (Polychromatic418967fa.accept_21_6_13_4_1_6521 48 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 181 235 (accept_3_3 47 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 45
  181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 235 (accept_3_3 44
  181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 43 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 235 (accept_3_3 41 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 181 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 235 (Polychromatic418967fa.accept_10_9_1_5_1_594
  39 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 235 (accept_3_3 38
  181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 181 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 235 (accept_3_3 35 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 235 (Polychromatic418967fa.accept_7_5_6_4_1_117
  33 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 235 (accept_3_3 32
  181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 235 (accept_3_3 29 181 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 181 235 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 181 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 235
  (Polychromatic418967fa.accept_20_7_1_15_1_2700 27 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 235 (accept_3_3 26 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 235 (Polychromatic418967fa.accept_16_9_5_11_1_3776 25 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 235 (accept_3_3 23 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 181 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 21 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 235 (accept_3_3 20 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 235 (accept_3_3 17 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 181 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 235
  (Polychromatic418967fa.accept_13_2_12_1_1_343 15 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 235 (accept_3_3 14 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 235 (accept_3_3 11 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 235 (accept_3_3 8 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 235 (accept_3_3 5 181 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 181 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 235 (accept_3_3 2 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 235 (Polychromatic418967fa.accept_19_1_10_7_1_14087 1 181 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 235))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 180 235 (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 180 235 5 11 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 180 235 (Polychromatic418967fa.accept_16_6_4_11_1_1719 54 180 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 180 235 (accept_3_3 53 180 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 180 235 (Polychromatic418967fa.accept_17_1_10_14_1_1173 52 180
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 180 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 180 235 5 10 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 180 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 49 180 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 180 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 180 235 (accept_3_3 47 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 180 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 46 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 180 235 5 9 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 180 235 (accept_3_3 44 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 180 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 180 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 180
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 180 235 (accept_3_3 41 180
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 235 5 8 36 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 235
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 180 235 (accept_3_3 38 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 180 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 180 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 180 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 180 235 5 7 36 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 180 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 180 235 (Polychromatic418967fa.accept_13_7_11_1_1_2903 33 180 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 235 (accept_3_3 32 180 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 180 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 180 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 235 5 6 36 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 235 (accept_3_3 29 180 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 235 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 180
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 180 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 180 235 (accept_3_3 26 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  180 235 5 5 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 180 235 (Polychromatic418967fa.accept_16_8_4_11_1_2687 24 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 180 235 (accept_3_3 23 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 180 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 180 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 235 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 180
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 235 5 4 36 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 235
  (Polychromatic418967fa.accept_21_19_12_4_1_8134 19 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 180 235 (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 180 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 180 235 (accept_3_3 17 180 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 180 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 180 235 5 3 36 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 180 235 (accept_3_3 14
  180 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 180 235 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 180 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 235 (accept_3_3 11 180 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 235 5 2 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 235 (accept_3_3 8 180 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 180 235 5 1 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 180 235 (Polychromatic418967fa.accept_23_4_19_5_1_14120 4 180 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 180
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 235 (accept_3_3 2 180 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  180 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 179 235 (Eq.refl Bool.true) (allA_of_3_1 57
  179 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 178 235 (Eq.refl Bool.true) (allA_succ_of_accept 57
  178 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 178 235 (accept_3_3 56 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 178 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 178 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 178 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 54 178 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 178 235 (accept_3_3 53 178 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 178 235 (Polychromatic418967fa.accept_10_2_8_5_1_587
  52 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 178 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 178 235 (accept_3_3 50 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 178 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 178 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 178 235 (accept_3_3 47 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 178 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 46 178 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 178 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 178 235 (accept_3_3 44 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 178 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 178 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 178 235 (accept_3_3 41 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 178 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 178 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 178 235 (accept_3_3 38 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 178 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 178 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 178 235 (accept_3_3 35 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 178 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 178 235 (accept_3_3 32 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 178 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 178 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 235 (accept_3_3 29 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 178 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 178 235 (accept_3_3 26 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 178 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 235 (accept_3_3 23 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 235 (accept_3_3 20 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 235 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 235 (accept_3_3 17 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 178
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 235 (accept_3_3 14 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 235 (accept_3_3 11 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 235 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 178 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 235 (accept_3_3 8 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 235 (accept_3_3 5 178 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 178 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 235 (accept_3_3 2 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 177 235
  (Eq.refl Bool.true) (allA_succ_of_accept 58 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 177 235 (accept_3_3 56 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 177 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 235 (accept_3_3 53 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 51 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 177 235 (accept_3_3 50 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 177 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 177 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 235 (accept_3_3 47 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 235
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 177 235 (accept_3_3 44 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 177 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 235 (accept_3_3 41 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 177 235 (accept_3_3 38 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 177 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 177 235 (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 235 (accept_3_3 35 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 177 235 (accept_3_3 32 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 177 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 235 (accept_3_3 29 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 177 235 (accept_3_3 26 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 177 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 235 (accept_3_3 23 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 235 (accept_3_3 20 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 235 (accept_3_3 17 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 235 (accept_3_3 14 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 235 (accept_3_3 11 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 235
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 235 (accept_3_3 8 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 235 (accept_3_3 5 177 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 235 (accept_3_3 2 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 235 (Polychromatic418967fa.accept_19_1_6_7_1_2019 1 177 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 176 235
  (Eq.refl Bool.true) (allA_of_3_1 60 176 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 175 235 (Eq.refl
  Bool.true) (allA_succ_of_gcd 60 175 235 5 12 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 175 235 (accept_3_3 59 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 175 235 (Polychromatic418967fa.accept_16_10_15_11_1_3785 58 175 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 57
  175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 175 235 (accept_3_3 56
  175 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 175 235 5 11 35 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 175 235
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 175 235 (accept_3_3 53 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 175 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 175 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 175 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 175 235 5 10 35 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 175 235
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 175 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 235 (accept_3_3 47 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 175 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 46 175 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 175 235 5 9 35 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 175 235 (accept_3_3 44 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 235 (Polychromatic418967fa.accept_9_7_4_1_1_391
  43 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 235 (accept_3_3 41 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  175 235 5 8 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 175 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 175 235 (accept_3_3 38 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 175 235 (Polychromatic418967fa.accept_21_16_7_4_1_3448 37 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 175 235 5 7 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 175 235
  (Polychromatic418967fa.accept_9_7_4_1_1_391 34 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 175 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 235 (accept_3_3 32 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 175 235 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 175 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 175 235 5 6 35 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 175 235 (accept_3_3 29 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 235 (Polychromatic418967fa.accept_8_4_7_3_1_144
  28 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 235
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 235 (accept_3_3 26 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  175 235 5 5 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 175 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 175 235 (accept_3_3 23 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 175 235 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 175 235 5 4 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 235
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 235 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 175 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 235 (accept_3_3 17 175 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 175 235 5 3 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 175 235 (accept_3_3 14
  175 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 235
  (Polychromatic418967fa.accept_19_13_4_7_1_5878 13 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 175 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 235 (accept_3_3 11 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 175 235 5 2 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 175 235 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 175 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 235 (accept_3_3 8 175 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 175 235 5 1 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 175 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 175 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 235 (accept_3_3 2 175 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 235 (Polychromatic418967fa.accept_16_1_15_11_1_356
  1 175 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 174 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 174 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 174 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 174 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 174 235 (accept_3_3 59 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 174 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 58
  174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 174 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 174 235 (accept_3_3 56 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 174 235 (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 174 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 174 235 (accept_3_3 53 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 174 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 174 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 174 235 (accept_3_3 50 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 174 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 174 235 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 174 235 (accept_3_3 47 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 174
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 174 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 174 235 (accept_3_3 44 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 174 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 174 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 174 235 (accept_3_3 41 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 174 235
  (Polychromatic418967fa.accept_10_9_4_5_1_616 39 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 174 235 (accept_3_3 38 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 174 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 174 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 235 (accept_3_3 35 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 174 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 174 235 (accept_3_3 32 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 174 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 174 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 235 (accept_3_3 29 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 235 (Polychromatic418967fa.accept_20_8_14_15_1_6932 28 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 174 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 174 235 (accept_3_3 26 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 174 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 235 (accept_3_3 23 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 235 (Polychromatic418967fa.accept_9_4_3_1_1_154
  22 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 174 235 (accept_3_3 20 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 174 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 174 235 (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 235 (accept_3_3 17 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 174 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 174 235 (accept_3_3 14 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 174 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 174 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 235 (accept_3_3 11 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 174 235 (accept_3_3 8 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  174 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 174 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 235 (accept_3_3 5 174 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 174 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 174 235 (accept_3_3 2 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  174 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 173 235
  (Eq.refl Bool.true) (allA_of_3_1 63 173 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 172 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 63 172 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 172 235 (accept_3_3 62 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 172 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 172 235
  (Polychromatic418967fa.accept_23_14_11_5_1_7453 60 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 172 235 (accept_3_3 59 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 172 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 172 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 172 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 172 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 172 235 (accept_3_3 56 172 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 172 235 (Polychromatic418967fa.accept_8_7_4_3_1_156
  55 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 172 235
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 54 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 172 235 (accept_3_3 53 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 172 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 52 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 172 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 172 235 (accept_3_3 50 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 172 235 (Polychromatic418967fa.accept_14_7_4_11_1_3038 49 172 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 172 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 172 235 (accept_3_3 47 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 172 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 172 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 172 235 (accept_3_3 44 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 172 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 172 235
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 172 235 (accept_3_3 41 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 172 235 (Polychromatic418967fa.accept_16_8_12_11_1_3697 40 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39
  172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 172 235 (accept_3_3 38
  172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 172 235
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 172 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 172 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 235 (accept_3_3 35 172 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 172 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 235 (accept_3_3 32 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 235 (accept_3_3 29 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 172
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 235 (accept_3_3 26 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 235 (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 235 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 235 (accept_3_3 23 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 172
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 235 (accept_3_3 20 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 235 (accept_3_3 17 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 172
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 235 (accept_3_3 14 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 235 (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 235 (accept_3_3 11 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 172
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 235 (accept_3_3 8 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 6 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 235 (accept_3_3 5 172 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 235 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 172 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 235 (accept_3_3 2 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 1 172 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 171 235
  (Eq.refl Bool.true) (allA_succ_of_accept 64 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 235
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 171 235 (accept_3_3 62 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 171 235 (Polychromatic418967fa.accept_13_9_2_1_1_813 61 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 171 235 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 235 (accept_3_3 59 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 171 235 (accept_3_3 56 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 171 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 171 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 235 (accept_3_3 53 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 235
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 171 235 (accept_3_3 50 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 171 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 171 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 171 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 235 (accept_3_3 47 171 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 171 235 (accept_3_3 44 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 171 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 171 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 235 (accept_3_3 41 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 171 235 (accept_3_3 38 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 171 235 (Polychromatic418967fa.accept_25_12_21_10_1_14119 37 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 235 (accept_3_3 35 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 235 (accept_3_3 32 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 31 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 235 (Polychromatic418967fa.accept_17_13_1_14_1_1149 30 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 235 (accept_3_3 29 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 171 235 (accept_3_3 26 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 171 235 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 171 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 235 (accept_3_3 23 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 235 (accept_3_3 20 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 235 (accept_3_3 17 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 235 (accept_3_3 14 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 235 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 235 (accept_3_3 11 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 171 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 235
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 235 (accept_3_3 8 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 171 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 235 (accept_3_3 5 171 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 235
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 235 (accept_3_3 2 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 171 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 170 235
  (Eq.refl Bool.true) (allA_of_3_1 66 170 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 169 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 169 235 (accept_3_3 65 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 169 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 235
  (Polychromatic418967fa.accept_20_3_9_15_1_6847 63 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 235 (accept_3_3 62 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 235 (accept_3_3 59 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 235 (accept_3_3 56 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 235 (Polychromatic418967fa.accept_21_13_1_4_1_11182 55 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 235 (accept_3_3 53 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 235 (accept_3_3 50 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 235 (accept_3_3 47 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 235 (accept_3_3 44 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 235 (accept_3_3 41 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 235 (accept_3_3 38 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 235 (accept_3_3 35 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 235 (accept_3_3 32 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 235 (accept_3_3 29 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 169 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 235
  (Polychromatic418967fa.accept_23_4_8_5_1_7448 27 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 235 (accept_3_3 26 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 235 (Polychromatic418967fa.accept_17_8_16_14_1_4261 25 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 235 (accept_3_3 23 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 235 (accept_3_3 20 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 235 (accept_3_3 17 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 235 (accept_3_3 14 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 235 (accept_3_3 11 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 235
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 235 (accept_3_3 8 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 235 (accept_3_3 5 169 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 169 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 235 (accept_3_3 2 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 169 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 168
  235 (Eq.refl Bool.true) (allA_succ_of_accept 67 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 168 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 168 235 (accept_3_3 65 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 168 235 (Polychromatic418967fa.accept_23_18_7_5_1_7475 64 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 168 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 168 235 (accept_3_3 62 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 168 235
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 168 235 (accept_3_3 59 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 168 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 168 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 168 235 (accept_3_3 56 168 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 168 235 (Polychromatic418967fa.accept_19_17_16_7_1_7213 55 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 168 235
  (Polychromatic418967fa.accept_13_2_12_1_1_343 54 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 168 235 (accept_3_3 53 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 168 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 51 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 235 (accept_3_3 50 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 168 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 168 235 (accept_3_3 47 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 168 235 (Polychromatic418967fa.accept_17_12_15_14_1_6746 46 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 235 (Polychromatic418967fa.accept_16_13_8_11_1_4785 45 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 235 (accept_3_3 44 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709
  43 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 168 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 168 235 (accept_3_3 41 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 168 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 168 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 235 (accept_3_3 38 168 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 168 235 (accept_3_3 35 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 168 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 235 (accept_3_3 32 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 168 235 (accept_3_3 29 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 168 235 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 168 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 235 (accept_3_3 26 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 235
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 168 235 (accept_3_3 23 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 168 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 235 (accept_3_3 20 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 235
  (Polychromatic418967fa.accept_16_3_8_11_1_2714 19 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 168 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 168 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 235 (accept_3_3 17 168 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 168 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 235 (Polychromatic418967fa.accept_13_2_12_1_1_343
  15 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 235 (accept_3_3 14
  168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 168 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 168 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 235 (accept_3_3 11 168 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 168 235 (Polychromatic418967fa.accept_19_10_16_7_1_10039 10 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 235
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 168 235 (accept_3_3 8 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  168 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 168 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 235 (accept_3_3 5 168 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 168 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 235 (accept_3_3 2 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 235 (Polychromatic418967fa.accept_22_1_14_15_1_12583 1 168 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 167
  235 (Eq.refl Bool.true) (allA_of_3_1 69 167 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 166 235
  (Eq.refl Bool.true) (allA_succ_of_accept 69 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 166 235 (accept_3_3 68 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 166 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 166
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 166 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 166 235 (accept_3_3 65 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 166 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 166 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 166 235 (accept_3_3 62 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 166 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 166 235 (accept_3_3 59 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 166 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 166 235 (accept_3_3 56 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 166 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 166 235
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 166 235 (accept_3_3 53 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 166 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 166 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 166 235 (accept_3_3 50 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 166 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 166 235 (accept_3_3 47 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 166 235 (Polychromatic418967fa.accept_19_8_14_7_1_10047 46 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 235 (accept_3_3 44 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 166 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 166 235 (accept_3_3 41 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 166 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 166 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 235 (accept_3_3 38 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 166 235 (accept_3_3 35 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 166 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 235 (accept_3_3 32 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 235 (accept_3_3 29 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 235 (accept_3_3 26 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 235 (accept_3_3 23 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 235 (accept_3_3 20 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 235
  (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 235 (accept_3_3 17 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 235 (accept_3_3 14 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 235 (accept_3_3 11 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 235 (Polychromatic418967fa.accept_17_10_13_14_1_3094 10 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 235 (accept_3_3 8 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 166 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 235 (accept_3_3 5 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 166 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 235 (accept_3_3 2 166 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 165 235 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 165 235 5 14 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 165 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 235 (accept_3_3 68 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 165 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 165 235 5 13 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 165 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 165 235 (Polychromatic418967fa.accept_12_3_9_7_1_472
  63 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 235 (accept_3_3 62
  165 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 235
  (Polychromatic418967fa.accept_9_7_3_1_1_386 61 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 235 5 12 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 235 (accept_3_3 59 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 57 165
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 235 (accept_3_3 56 165
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 165 235 5 11 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 165 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 235 (accept_3_3 53 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 165 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 165 235 5 10 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 165 235
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 165 235 (Polychromatic418967fa.accept_18_12_3_1_1_3685 48 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 235 (accept_3_3 47 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 165 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 235 5 9 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 235 (accept_3_3 44 165 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 165 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 235 (accept_3_3 41 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  165 235 5 8 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 165 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 235 (accept_3_3 38 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 235 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 235 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 165
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 165 235 5 7 33 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 165 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 235 (accept_3_3 32 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 165 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 235 5 6 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 235 (accept_3_3 29 165 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 235 (accept_3_3 26 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  165 235 5 5 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 165 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 235 (accept_3_3 23 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 235 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 165
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 165 235 5 4 33 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 235
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 165 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 235 (accept_3_3 17 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 165 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 235 5 3 33 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 235 (accept_3_3 14 165 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 165 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 235
  (Polychromatic418967fa.accept_18_12_3_1_1_3685 12 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 235 (accept_3_3 11 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  165 235 5 2 33 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 165 235 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 235 (accept_3_3 8 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 235 5 1 33 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 165 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 235 (accept_3_3 2 165 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 165 235 (Polychromatic418967fa.accept_19_1_13_7_1_993 1 165 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 164 235 (Eq.refl Bool.true)
  (allA_of_3_1 72 164 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 163 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 163 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 163 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 163 235 (accept_3_3 71 163 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 163 235 (Polychromatic418967fa.accept_16_6_3_11_1_3751 70 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 163 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 163 235 (accept_3_3 68 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 163 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 163 235 (Polychromatic418967fa.accept_19_9_11_7_1_5836 66 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 163 235 (accept_3_3 65 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 163 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 163
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 235
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 63 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 163 235 (accept_3_3 62 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 163 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 163 235 (Polychromatic418967fa.accept_13_8_7_1_1_1385 60 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 163 235 (accept_3_3 59 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 163 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 58 163
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 57 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 163 235 (accept_3_3 56 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 163 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 163 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 235 (accept_3_3 53 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 235
  (Polychromatic418967fa.accept_19_13_11_7_1_4451 51 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 163 235 (accept_3_3 50 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 163 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 235 (Polychromatic418967fa.accept_7_6_2_4_1_291
  48 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 235 (accept_3_3 47
  163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 235
  (Polychromatic418967fa.accept_11_2_9_4_1_310 46 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 163 235 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 163 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 235 (accept_3_3 44 163 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 163 235 (Polychromatic418967fa.accept_23_20_2_5_1_14118 43 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 235
  (Polychromatic418967fa.accept_10_2_3_5_1_996 42 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 235 (accept_3_3 41 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 235 (Polychromatic418967fa.accept_16_7_3_11_1_3682 39 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 235 (accept_3_3 38 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 163
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 235
  (Polychromatic418967fa.accept_27_9_1_19_1_4355 36 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 235 (accept_3_3 35 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 235 (accept_3_3 32 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 163 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 235
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 235 (accept_3_3 29 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 235 (accept_3_3 26 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 235 (Polychromatic418967fa.accept_20_5_3_15_1_6909 25 163 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 235
  (Polychromatic418967fa.accept_11_2_9_4_1_310 24 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 235 (accept_3_3 23 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 235 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 235 (accept_3_3 20 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 235
  (Polychromatic418967fa.accept_10_8_3_5_1_613 18 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 235 (accept_3_3 17 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 235 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 235 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 235 (accept_3_3 14 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 163 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 235 (accept_3_3 11 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 235 (Polychromatic418967fa.accept_20_10_3_15_1_1546 10 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 235 (Polychromatic418967fa.accept_19_9_11_7_1_5836 9 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 235 (accept_3_3 8 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 163 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 235 (accept_3_3 5 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 163 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 235 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 235 (accept_3_3 2 163 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 163 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 162 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 162 235 (Polychromatic418967fa.accept_13_7_6_1_1_368
  72 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 162 235 (accept_3_3 71
  162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 162 235
  (Polychromatic418967fa.accept_13_5_6_1_1_822 70 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 162 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 162 235 (accept_3_3 68 162 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 162 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 67 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 162 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 162 235 (accept_3_3 65 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 162 235 (Polychromatic418967fa.accept_20_4_2_15_1_6904 64 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 162 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 162 235 (accept_3_3 62 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 162 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 235
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 162 235 (accept_3_3 59 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 162 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 235 (accept_3_3 56 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 162 235 (accept_3_3 53 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 162 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 162 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 235 (accept_3_3 50 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 162 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 235 (accept_3_3 47 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 162 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 46 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 235 (accept_3_3 44 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 235
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 162 235 (accept_3_3 41 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 162 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 162 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 235 (accept_3_3 38 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 162 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 235 (accept_3_3 35 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 162 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 235 (accept_3_3 32 162 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 235 (Polychromatic418967fa.accept_7_3_1_4_1_121
  31 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 235
  (Polychromatic418967fa.accept_20_10_2_15_1_1517 30 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 162 235 (accept_3_3 29 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 162 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 162 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 162
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 235 (accept_3_3 26 162
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9
  25 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 235 (accept_3_3 23 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 235 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 235 (accept_3_3 20 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 235 (accept_3_3 17 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 235 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 235 (accept_3_3 14 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 235 (accept_3_3 11 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 235 (accept_3_3 8 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 235 (accept_3_3 5 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 235 (Polychromatic418967fa.accept_14_4_8_11_1_794 4 162 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 235 (accept_3_3 2 162 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 161 235 (Eq.refl
  Bool.true) (allA_of_3_1 75 161 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 160 235 (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 160 235 5 15 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 160 235 (accept_3_3 74 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 160 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 160 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 160 235 (accept_3_3 71 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 160 235 5 14 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 160 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 160 235 (accept_3_3 68 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 160 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 160 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 160 235 5 13 32 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 160 235
  (Polychromatic418967fa.accept_18_10_16_1_1_1534 64 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 160 235 (accept_3_3 62 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 160 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 160 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 160 235 5 12 32 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 160 235 (accept_3_3 59 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 160 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 58
  160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 160 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 160 235 (accept_3_3 56 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  160 235 5 11 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 160 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 235 (accept_3_3 53 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 160 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51
  160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 235 5 10 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 235
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 160 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 235 (accept_3_3 47 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 160 235 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 160 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 160 235 5 9 32 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 160 235 (accept_3_3 44 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 235
  (Polychromatic418967fa.accept_18_7_16_1_1_4951 43 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 160 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 235 (accept_3_3 41 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 160 235 5 8 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 235 (accept_3_3 38 160 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 235
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 160 235 5 7 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 160 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 235 (accept_3_3 32 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 235 5 6 32 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 235 (accept_3_3 29
  160 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 235
  (Polychromatic418967fa.accept_18_10_16_1_1_1534 28 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 235 (accept_3_3 26 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 160 235 5 5 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 160 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 235 (accept_3_3 23 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 235 (Polychromatic418967fa.accept_9_4_7_1_1_379
  22 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 235 5 4 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 160 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 235 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 160
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 235 (accept_3_3 17 160
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 160 235 5 3 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 160 235 (accept_3_3 14 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 160 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 235 (accept_3_3 11 160 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 235 5 2 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 235 (accept_3_3 8 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 235 (Polychromatic418967fa.accept_18_7_16_1_1_4951
  7 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 160 235 5 1 32 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 160 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 160 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 235 (accept_3_3 2 160 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 235 (Polychromatic418967fa.accept_19_1_8_7_1_4470
  1 160 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 159 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 159 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 75
  159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 235 (accept_3_3 74
  159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 235
  (Polychromatic418967fa.accept_28_17_19_11_1_14117 73 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 159 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 159 235 (accept_3_3 71 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 159 235 (accept_3_3 68 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 159 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 159 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 235 (accept_3_3 65 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 235
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 159 235 (accept_3_3 62 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 159 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 159 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 235 (accept_3_3 59 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 159 235 (accept_3_3 56 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 159 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 159 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 235 (accept_3_3 53 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 159 235 (accept_3_3 50 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 159 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 159 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 235 (accept_3_3 47 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 159 235 (accept_3_3 44 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 159 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 159 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 235 (accept_3_3 41 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 159 235 (accept_3_3 38 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 159 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 159 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 235 (accept_3_3 35 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 159 235 (accept_3_3 32 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 159 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 235 (accept_3_3 29 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 235 (accept_3_3 26 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 235 (accept_3_3 23 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 235 (accept_3_3 20 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 235 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 235 (accept_3_3 17 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 235 (accept_3_3 14 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 235 (accept_3_3 11 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 235 (accept_3_3 8 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 235 (accept_3_3 5 159 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 235 (accept_3_3 2 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 159 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 158 235 (Eq.refl Bool.true) (allA_of_3_1 78 158 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 157 235
  (Eq.refl Bool.true) (allA_succ_of_accept 78 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 157 235 (accept_3_3 77 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 157 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 157 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 157 235 (accept_3_3 74 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 157 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 157 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 157 235 (accept_3_3 71 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 157 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 157 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 157 235 (accept_3_3 68 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 157 235 (Polychromatic418967fa.accept_19_10_5_7_1_10007 67 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 235 (accept_3_3 65 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 235 (accept_3_3 62 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 235 (accept_3_3 59 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 235 (accept_3_3 56 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 235 (accept_3_3 53 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 235 (accept_3_3 50 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 235 (Polychromatic418967fa.accept_14_7_3_11_1_2199 49 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 235 (accept_3_3 47 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 235
  (Polychromatic418967fa.accept_20_5_17_15_1_6858 45 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 157 235 (accept_3_3 44 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 157 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 157 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 235 (accept_3_3 41 157 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 235 (Polychromatic418967fa.accept_11_7_3_4_1_729
  40 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 235 (accept_3_3 38 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 235 (Polychromatic418967fa.accept_21_16_10_4_1_3433 37 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 235 (accept_3_3 35 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 235 (accept_3_3 32 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 235 (accept_3_3 29 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 235 (accept_3_3 26 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 235 (accept_3_3 23 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 235 (accept_3_3 20 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 235 (accept_3_3 17 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 235 (accept_3_3 14 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 235 (accept_3_3 11 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 235
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 235 (accept_3_3 8 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 235 (accept_3_3 5 157 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 157 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 235 (accept_3_3 2 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 156 235 (Eq.refl Bool.true) (allA_succ_of_accept 79 156 235 (Polychromatic418967fa.accept_8_7_4_3_1_156
  79 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 156 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 156 235 (accept_3_3 77 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 156 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 156 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 156 235 (accept_3_3 74 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 156 235 (Polychromatic418967fa.accept_19_16_4_7_1_5879 73 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 156 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 72 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 156 235 (accept_3_3 71 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 156 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 156 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 156 235 (accept_3_3 68 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 156 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 156 235
  (Polychromatic418967fa.accept_17_15_3_14_1_4230 66 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 156 235 (accept_3_3 65 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 156 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 156 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 156 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 235 (accept_3_3 62 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 235 (Polychromatic418967fa.accept_7_5_2_4_1_126
  61 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 156 235 (accept_3_3 59 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 156 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 156 235 (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 235 (accept_3_3 56 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 156 235 (accept_3_3 53 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 156 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 156 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 235 (accept_3_3 50 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 235 (accept_3_3 47 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 156 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 235 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 235 (accept_3_3 44 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 235 (accept_3_3 41 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 235 (accept_3_3 38 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 235 (Polychromatic418967fa.accept_14_9_2_11_1_780 37 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 235
  (Polychromatic418967fa.accept_16_4_12_11_1_2650 36 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 156 235 (accept_3_3 35 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 156 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 156 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 156 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 235 (accept_3_3 32 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 235 (Polychromatic418967fa.accept_8_7_4_3_1_156
  31 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 235
  (Polychromatic418967fa.accept_19_11_4_7_1_1029 30 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 156 235 (accept_3_3 29 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 156 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 28 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 156 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 235 (accept_3_3 26 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 235 (accept_3_3 23 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 235 (accept_3_3 20 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 235
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 235 (accept_3_3 17 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 235 (accept_3_3 14 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 235 (accept_3_3 11 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 235 (Polychromatic418967fa.accept_16_10_12_11_1_346 10 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 235 (accept_3_3 8 156 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 235 (accept_3_3 5 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 156 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 235 (accept_3_3 2 156 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 156 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 155 235 (Eq.refl
  Bool.true) (allA_of_3_1 81 155 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 154 235 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 154 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 154 235 (accept_3_3 80 154 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 154 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 79 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 154 235
  (Polychromatic418967fa.accept_17_10_1_14_1_489 78 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 154 235 (accept_3_3 77 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 154 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 154 235 (accept_3_3 74 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 154 235
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 154 235 (accept_3_3 71 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 154 235 (Polychromatic418967fa.accept_18_16_10_1_1_3696 70 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 235 (accept_3_3 68 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 154 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 67 154 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 154 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 154 235 (accept_3_3 65 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 154 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 154 235 (accept_3_3 62 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 235
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 154 235 (accept_3_3 59 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 154 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 58 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 154 235 (accept_3_3 56 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 154 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 55 154 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 235
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 154 235 (accept_3_3 53 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 154 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 235 (accept_3_3 50 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 235
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 48 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 154 235 (accept_3_3 47 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 154 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 235 (accept_3_3 44 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 154 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 154 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 154 235
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 154 235 (accept_3_3 41 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 154 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 235 (accept_3_3 38 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 154 235 (accept_3_3 35 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 154 235 (Polychromatic418967fa.accept_13_8_11_1_1_3789 34 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 235 (accept_3_3 32 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 235
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 30 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 154 235 (accept_3_3 29 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 154 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 154 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 154 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 235 (accept_3_3 26 154 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25
  154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 235
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 24 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 235 (accept_3_3 23 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 235 (Polychromatic418967fa.accept_13_9_11_1_1_1375 22 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 235 (accept_3_3 20 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 235
  (Polychromatic418967fa.accept_21_18_7_4_1_8131 18 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 235 (accept_3_3 17 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 235 (accept_3_3 14 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 235
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 154 235 (accept_3_3 11 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 154 235 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 235 (accept_3_3 8 154
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 235
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 154 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 154 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 235 (accept_3_3 5 154 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 154 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 154 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3
  154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 235 (accept_3_3 2 154
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 235 (Polychromatic418967fa.accept_4_1_2_3_1_9
  1 154 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 153 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 81 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 153 235 (accept_3_3 80 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 153 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 153 235 (accept_3_3 77 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 153 235 (accept_3_3 74 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 153 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 153 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 235 (accept_3_3 71 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 235
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 69 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 235 (accept_3_3 68 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 153 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 235 (accept_3_3 65 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 235 (accept_3_3 62 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 60 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 235 (accept_3_3 59 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 57 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 235 (accept_3_3 56 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 235 (Polychromatic418967fa.accept_21_13_6_4_1_2178 55 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 235 (accept_3_3 53 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 235 (accept_3_3 50 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 153 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 49 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 235 (accept_3_3 47 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 235 (accept_3_3 44 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 153 235 (Polychromatic418967fa.accept_13_4_10_1_1_1390 43 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 235 (accept_3_3 41 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 235 (accept_3_3 38 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 235 (accept_3_3 35 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 235 (accept_3_3 32 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 153 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 235 (accept_3_3 29 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 235
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 235 (accept_3_3 26 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 235 (Polychromatic418967fa.accept_19_6_1_7_1_5872 25 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 235 (accept_3_3 23 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 235 (accept_3_3 20 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 235 (accept_3_3 17 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 235
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 235 (accept_3_3 14 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 235 (accept_3_3 11 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 235 (accept_3_3 8 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 235 (accept_3_3 5 153 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 235 (accept_3_3 2 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 235 (Polychromatic418967fa.accept_24_1_9_19_1_12488 1 153 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 152 235 (Eq.refl Bool.true) (allA_of_3_1 84 152 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 151 235 (Eq.refl Bool.true) (allA_succ_of_accept 84 151 235 (Polychromatic418967fa.accept_8_4_7_3_1_144
  84 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 151 235 (accept_3_3 83
  151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 151 235
  (Polychromatic418967fa.accept_15_7_1_10_1_305 82 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 151 235 (Polychromatic418967fa.accept_15_6_1_10_1_1549 81 151 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 235 (accept_3_3 80 151 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 151 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 79 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 151 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 151 235 (accept_3_3 77 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 151 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 151 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 151 235 (accept_3_3 74 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 151 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 73 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 151 235
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 72 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 151 235 (accept_3_3 71 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 151 235 (Polychromatic418967fa.accept_13_5_8_1_1_2161 70 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 151 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 235 (accept_3_3 68 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 235 (accept_3_3 65 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 64 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 235 (accept_3_3 62 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 235 (Polychromatic418967fa.accept_13_9_8_1_1_824 61 151
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 235 (accept_3_3 59 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 235 (accept_3_3 56 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 235 (Polychromatic418967fa.accept_19_17_18_7_1_11434 55 151 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 235
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 235 (accept_3_3 53 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 52 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 235 (accept_3_3 50 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 235 (accept_3_3 47 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 235 (accept_3_3 44 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 151
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 235 (accept_3_3 41 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 235 (accept_3_3 38 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 235 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 151 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 235 (accept_3_3 35 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 235 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 235 (accept_3_3 32 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 235 (accept_3_3 29 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 235 (Polychromatic418967fa.accept_19_8_18_7_1_3143 27 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 235 (accept_3_3 26 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 235 (Polychromatic418967fa.accept_13_12_8_1_1_825 25 151
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 235 (accept_3_3 23 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 235 (accept_3_3 20 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 235
  (Polychromatic418967fa.accept_11_7_8_4_1_718 18 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 235 (accept_3_3 17 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 235 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 235 (accept_3_3 14 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 235 (accept_3_3 11 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 235 (Polychromatic418967fa.accept_19_10_18_7_1_12729 10 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 235 (accept_3_3 8 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 151 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 235 (accept_3_3 5 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 151 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 235 (accept_3_3 2 151 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 151 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 150 235
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 150 235 5 17 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 150 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 150 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 150 235 (accept_3_3 83 150 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 150 235
  (Polychromatic418967fa.accept_16_2_6_11_1_1722 82 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 150 235 5 16 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 79
  150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 150 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 150 235 (accept_3_3 77 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 150 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 150 235 5 15 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 150 235 (accept_3_3 74 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 150 235 (Polychromatic418967fa.accept_19_15_17_7_1_8734 72 150
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 150 235 (accept_3_3 71 150
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 235 5 14 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 150 235 (accept_3_3 68 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 150 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 150 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 150 235 5 13 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 150 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 64 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 150 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 235 (accept_3_3 62 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 235 5 12 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 235 (accept_3_3 59 150 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 150 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 150 235 (accept_3_3 56 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  150 235 5 11 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 150 235 (Polychromatic418967fa.accept_19_16_17_7_1_5845 54 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 150 235 (accept_3_3 53 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 150 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 235
  (Polychromatic418967fa.accept_16_3_6_11_1_2718 51 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 235 5 10 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 235 (Polychromatic418967fa.accept_7_6_3_4_1_294
  48 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 235 (accept_3_3 47
  150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 235
  (Polychromatic418967fa.accept_20_6_10_15_1_6879 46 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 150 235 5 9 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 150 235 (accept_3_3 44 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 235 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 150
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 235 (accept_3_3 41 150
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 235 5 8 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 150 235 (accept_3_3 38 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 150 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 150 235 5 7 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 150 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 235 (accept_3_3 32 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 150 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 235 5 6 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 235 (accept_3_3 29 150 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 235 (Polychromatic418967fa.accept_19_9_17_7_1_12793 28 150
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 150 235 (accept_3_3 26 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  150 235 5 5 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 150 235 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 235 (accept_3_3 23 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 235 5 4 30 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 235
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 150 235 (Polychromatic418967fa.accept_16_2_6_11_1_1722 18 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 235 (accept_3_3 17 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 150 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 235 5 3 30 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 235 (accept_3_3 14 150 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 235 (accept_3_3 11 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  150 235 5 2 30 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 235 (accept_3_3 8 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 150 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 150 235 5 1 30 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 150 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 150 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 150 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 235 (accept_3_3 2 150 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 150 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 149 235
  (Eq.refl Bool.true) (allA_of_3_1 87 149 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 148 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 148 235 (accept_3_3 86 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 148 235 (Polychromatic418967fa.accept_20_5_8_15_1_9845 85 148 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 148 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 148 235 (accept_3_3 83 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 148 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 148 235 (accept_3_3 80 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 148 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 79 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 148 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 148 235 (accept_3_3 77 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 148 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 76 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 148 235 (accept_3_3 74 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 148 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 148 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 148 235 (accept_3_3 71 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 148 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 235 (accept_3_3 68 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 148 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 67 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 148 235 (accept_3_3 65 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 148 235 (Polychromatic418967fa.accept_13_12_5_1_1_1383 64 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 235 (accept_3_3 62 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 148 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 235 (accept_3_3 59 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 235 (accept_3_3 56 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 55 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 235 (accept_3_3 53 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 235 (accept_3_3 50 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 148 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 235 (accept_3_3 47 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 235 (accept_3_3 44 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 235 (accept_3_3 41 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 235 (accept_3_3 38 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 235 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 235
  (Polychromatic418967fa.accept_19_17_15_7_1_10030 36 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 148 235 (accept_3_3 35 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 148 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 148 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 235 (accept_3_3 32 148 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 235 (Polychromatic418967fa.accept_7_3_1_4_1_121
  31 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 235 (accept_3_3 29 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 235 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 235 (accept_3_3 26 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 235 (accept_3_3 23 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 235 (accept_3_3 20 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 235
  (Polychromatic418967fa.accept_14_4_8_11_1_794 18 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 235 (accept_3_3 17 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 235 (accept_3_3 14 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 235 (accept_3_3 11 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 235 (accept_3_3 8 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 235 (accept_3_3 5 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 235 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 148 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 235 (accept_3_3 2 148 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 148 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 147 235
  (Eq.refl Bool.true) (allA_succ_of_accept 88 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 147 235 (accept_3_3 86 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 147 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 147 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 84 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 235 (accept_3_3 83 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 81 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 147 235 (accept_3_3 80 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 147 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 147 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 235 (accept_3_3 77 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 235
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 75 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 147 235 (accept_3_3 74 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 147 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 147 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 235 (accept_3_3 71 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 235 (accept_3_3 68 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 147 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 235 (Polychromatic418967fa.accept_14_10_7_11_1_3015 66 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 235 (accept_3_3 65 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 147 235 (accept_3_3 62 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 147 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 147 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 235 (accept_3_3 59 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 235 (accept_3_3 56 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 235 (Polychromatic418967fa.accept_13_3_4_1_1_363 55 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 54 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 235 (accept_3_3 53 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 235 (accept_3_3 50 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 235 (accept_3_3 47 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 235 (accept_3_3 44 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 235 (accept_3_3 41 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 235
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 235 (accept_3_3 38 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 235 (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 235 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 235 (accept_3_3 35 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 235 (accept_3_3 32 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 235 (Polychromatic418967fa.accept_16_14_3_11_1_5969 30 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 235 (accept_3_3 29 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 235
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 27 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 235 (accept_3_3 26 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 235 (accept_3_3 23 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 235 (accept_3_3 20 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 235 (Polychromatic418967fa.accept_23_19_9_5_1_14090 19 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 235 (accept_3_3 17 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 235 (accept_3_3 14 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 235 (accept_3_3 11 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 235 (accept_3_3 8 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 235 (accept_3_3 5 147 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 235 (accept_3_3 2 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 235 (Polychromatic418967fa.accept_20_1_7_15_1_1521 1 147 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 90 146 235 (Eq.refl Bool.true) (allA_of_3_1 90 146 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 91 145 235 (Eq.refl Bool.true) (allA_succ_of_gcd 90 145 235 5 18 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 145 235 (accept_3_3 89 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 145 235 (Polychromatic418967fa.accept_20_8_5_15_1_9868 88 145
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 145 235
  (Polychromatic418967fa.accept_13_9_2_1_1_813 87 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 145 235 (accept_3_3 86 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85
  145 235 5 17 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 84 145 235 (Polychromatic418967fa.accept_13_6_2_1_1_2137 84 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 145 235 (accept_3_3 83 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 145 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907
  81 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 145 235 5 16 29 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 145 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 79 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 235 (accept_3_3 77 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 145 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 145 235 5 15 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 145 235 (accept_3_3 74 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 145 235 (Polychromatic418967fa.accept_17_5_9_14_1_4282 73 145
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 145 235 (accept_3_3 71 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  145 235 5 14 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 145 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 235 (accept_3_3 68 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 145 235 (Polychromatic418967fa.accept_20_7_5_15_1_1548 67 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 145 235 5 13 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 145 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 235
  (Polychromatic418967fa.accept_16_15_1_11_1_3747 63 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 145 235 (accept_3_3 62 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 145 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 61 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 145 235 5 12 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 145 235 (accept_3_3 59 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 235 (accept_3_3 56 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  145 235 5 11 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 235 (accept_3_3 53 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 145 235 (Polychromatic418967fa.accept_19_14_12_7_1_10027 52 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 145 235 5 10 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 145 235 (Polychromatic418967fa.accept_19_11_12_7_1_3188 49 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 235 (accept_3_3 47 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 145 235 5 9 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 145 235 (accept_3_3 44 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 145 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 235 (accept_3_3 41 145 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 145 235 5 8 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 145 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 39 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 235 (accept_3_3 38 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 235 5 7 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 235 (Polychromatic418967fa.accept_19_14_12_7_1_10027 33 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 235 (accept_3_3 32 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 31 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 235 5 6 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 235 (accept_3_3 29 145 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703
  28 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 235 (accept_3_3 26 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  145 235 5 5 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 145 235 (Polychromatic418967fa.accept_19_5_12_7_1_4416 24 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 235 (accept_3_3 23 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 235 (Polychromatic418967fa.accept_17_4_9_14_1_5406 21 145
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 235 5 4 29 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 235
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 235 (accept_3_3 17 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 145 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 145 235 5 3 29 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 145 235 (accept_3_3 14 145 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 235
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 235 (accept_3_3 11 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  145 235 5 2 29 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 145 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 145 235 (accept_3_3 8 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 145 235 (Polychromatic418967fa.accept_20_7_5_15_1_1548 7 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 235 5 1 29 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 235
  (Polychromatic418967fa.accept_17_4_9_14_1_5406 4 145 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 235 (accept_3_3 2 145 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 144 235
  (Eq.refl Bool.true) (allA_succ_of_accept 91 144 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 91 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 144 235
  (Polychromatic418967fa.accept_19_14_11_7_1_7236 90 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 144 235 (accept_3_3 89 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 144 235 (Polychromatic418967fa.accept_19_12_11_7_1_5837 88 144 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 144 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 87 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 144 235 (accept_3_3 86 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 144 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 85 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 144 235 (Polychromatic418967fa.accept_17_16_8_14_1_6757 84 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 144 235 (accept_3_3 83 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 235
  (Polychromatic418967fa.accept_20_2_4_15_1_6911 82 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 144 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 235 (accept_3_3 80 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 144 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 79 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 144 235
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 78 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 144 235 (accept_3_3 77 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 144 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 76 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 144 235 (Polychromatic418967fa.accept_17_7_8_14_1_6720 75 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 235 (accept_3_3 74 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 144 235 (Polychromatic418967fa.accept_22_7_12_15_1_14116 73
  144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 144 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 144 235 (accept_3_3 71 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 144 235 (Polychromatic418967fa.accept_19_13_11_7_1_4451 70 144 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 235 (Polychromatic418967fa.accept_10_9_4_5_1_616
  69 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 235 (accept_3_3 68
  144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 235
  (Polychromatic418967fa.accept_17_16_8_14_1_6757 67 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 144 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 66 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 144 235 (accept_3_3 65 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 64 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 144 235
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 144 235 (accept_3_3 62 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 144 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 61 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 144 235 (Polychromatic418967fa.accept_23_14_6_5_1_14115 60 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 144 235 (accept_3_3 59 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 235 (Polychromatic418967fa.accept_17_7_8_14_1_6720 58 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 235
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 57 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 144 235 (accept_3_3 56 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 144 235 (Polychromatic418967fa.accept_21_13_18_4_1_11181 55 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 235 (Polychromatic418967fa.accept_21_12_18_4_1_4955 54 144 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 235 (accept_3_3 53 144 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318
  52 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 235
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 144 235 (accept_3_3 50 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 144 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 144 235 (Polychromatic418967fa.accept_15_3_9_10_1_2325 48 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 235 (accept_3_3 47 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 235
  (Polychromatic418967fa.accept_17_11_8_14_1_8084 45 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 144 235 (accept_3_3 44 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 144 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 43 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 235 (accept_3_3 41 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 235
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 40 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 144 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 235 (accept_3_3 38 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 144 235 (Polychromatic418967fa.accept_19_18_11_7_1_11473 37 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 235
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 144 235 (accept_3_3 35 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 144 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 235 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 235 (accept_3_3 32 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 235
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 144 235 (accept_3_3 29 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 144 235 (Polychromatic418967fa.accept_17_11_8_14_1_8084 28 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 144 235 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 235 (accept_3_3 26 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 235 (Polychromatic418967fa.accept_20_5_4_15_1_3931 25 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 235
  (Polychromatic418967fa.accept_17_7_8_14_1_6720 24 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 144 235 (accept_3_3 23 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 144 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 235 (accept_3_3 20 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 144 235 (accept_3_3 17 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 144 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 144 235 (Polychromatic418967fa.accept_14_1_4_11_1_3036 15 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 235 (accept_3_3 14 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 235 (Polychromatic418967fa.accept_19_13_11_7_1_4451 13 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 144 235 (accept_3_3 11 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 235 (Polychromatic418967fa.accept_20_10_4_15_1_12657 10 144 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 9
  144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 235 (accept_3_3 8 144
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 235
  (Polychromatic418967fa.accept_14_7_4_11_1_3038 7 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 144 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 235 (accept_3_3 5 144 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 144 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 144 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 235
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 235 (accept_3_3 2 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 144 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 143 235
  (Eq.refl Bool.true) (allA_of_3_1 93 143 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 142 235 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 142 235 (accept_3_3 92 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 142 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 142 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 90 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 142 235 (accept_3_3 89 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 142 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 88 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 142 235 (accept_3_3 86 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 142 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 142 235 (accept_3_3 83 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 142 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 82 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 142 235 (accept_3_3 80 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 142 235 (Polychromatic418967fa.accept_14_9_2_11_1_780 79 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 142 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 142 235 (accept_3_3 77 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 142 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 76 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 142 235 (accept_3_3 74 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 142 235
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 142 235 (accept_3_3 71 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 142 235 (Polychromatic418967fa.accept_13_5_12_1_1_2123 70 142 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 142 235 (accept_3_3 68 142 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 142 235 (Polychromatic418967fa.accept_9_4_7_1_1_379
  67 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 142 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 142 235 (accept_3_3 65 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 64 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 235 (accept_3_3 62 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 235 (accept_3_3 59 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 235 (accept_3_3 56 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 235 (accept_3_3 53 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 235 (accept_3_3 50 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 235 (accept_3_3 47 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 46 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 235 (accept_3_3 44 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 235 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 235 (accept_3_3 41 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 235 (accept_3_3 38 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 235
  (Polychromatic418967fa.accept_19_17_9_7_1_3171 36 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 235 (accept_3_3 35 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 235 (accept_3_3 32 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 235 (accept_3_3 29 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 235 (accept_3_3 26 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 235 (accept_3_3 23 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 235 (accept_3_3 20 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 235 (accept_3_3 17 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 235 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 235 (accept_3_3 14 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 235 (accept_3_3 11 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 235 (Polychromatic418967fa.accept_18_10_16_1_1_1534 10 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 235 (accept_3_3 8 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 235 (accept_3_3 5 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 142 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 235 (accept_3_3 2 142 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 141
  235 (Eq.refl Bool.true) (allA_succ_of_gcd 94 141 235 47 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 141 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 235 (accept_3_3 92 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 235 (Polychromatic418967fa.accept_15_1_6_10_1_23
  91 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 141 235 (accept_3_3 89 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 141 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 235 (accept_3_3 86 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 141 235 (accept_3_3 83 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 141 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 81 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 235 (accept_3_3 80 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 141 235 (accept_3_3 77 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 235 (accept_3_3 74 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 235
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 72 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 235 (accept_3_3 71 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 235 (accept_3_3 68 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 235 (accept_3_3 65 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 235 (accept_3_3 62 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 235
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 60 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 235 (accept_3_3 59 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 235 (accept_3_3 56 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 235 (Polychromatic418967fa.accept_13_3_11_1_1_2122 55 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 235 (accept_3_3 53 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 51 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 235 (accept_3_3 50 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 47 141 235 47 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 46 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 235 (accept_3_3 44 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 235 (Polychromatic418967fa.accept_9_7_6_1_1_709
  43 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 235 (accept_3_3 41 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 235 (accept_3_3 38 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 235 (Polychromatic418967fa.accept_19_18_8_7_1_4446 37 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 235
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 141 235 (accept_3_3 35 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 235 (accept_3_3 32 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 235 (accept_3_3 29 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 235 (accept_3_3 26 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 235 (accept_3_3 23 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 235 (accept_3_3 20 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 235 (accept_3_3 17 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 235 (accept_3_3 14 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 141 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 235 (accept_3_3 11 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 235 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 235 (accept_3_3 8 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 235 (accept_3_3 5 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 235 (accept_3_3 2 141 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 141 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 140
  235 (Eq.refl Bool.true) (allA_of_3_1 96 140 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 139 235
  (Eq.refl Bool.true) (allA_succ_of_accept 96 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 139 235 (accept_3_3 95 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 139 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 139 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 93 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 139 235 (accept_3_3 92 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 139 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 139 235 (Polychromatic418967fa.accept_19_14_6_7_1_7223 90 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 139 235 (accept_3_3 89 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 139 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 88 139 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 139 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 139 235 (accept_3_3 86 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 139 235 (Polychromatic418967fa.accept_11_8_7_4_1_3011 85 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 139 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 235 (accept_3_3 83 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 139 235
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 139 235 (accept_3_3 80 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 139 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 139 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 78 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 235 (accept_3_3 77 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 76 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 235 (accept_3_3 74 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 235 (accept_3_3 71 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 69 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 235 (accept_3_3 68 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 67 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 235 (accept_3_3 65 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 235
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 63 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 235 (accept_3_3 62 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 235 (accept_3_3 59 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 235 (accept_3_3 56 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 235 (Polychromatic418967fa.accept_22_11_7_15_1_14114 55 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 235 (accept_3_3 53 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 139 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 235 (accept_3_3 50 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 235 (Polychromatic418967fa.accept_13_10_9_1_1_5609 49 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 235 (accept_3_3 47 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 46 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 235 (accept_3_3 44 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 235 (accept_3_3 41 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 235 (accept_3_3 38 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 235 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 235 (accept_3_3 35 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 139 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 235 (accept_3_3 32 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 235 (accept_3_3 29 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 235
  (Polychromatic418967fa.accept_19_8_6_7_1_7216 27 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 235 (accept_3_3 26 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 235 (accept_3_3 23 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 139 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 235 (accept_3_3 20 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 235 (accept_3_3 17 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 139 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 235 (accept_3_3 14 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 235 (accept_3_3 11 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 235 (accept_3_3 8 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 235 (accept_3_3 5 139 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 235 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 139 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 235 (accept_3_3 2 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 139 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  138 235 (Eq.refl Bool.true) (allA_succ_of_accept 97 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 138 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 138 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 138 235 (accept_3_3 95 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 138 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 94 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 138 235 (accept_3_3 92 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 138 235 (Polychromatic418967fa.accept_21_7_12_4_1_6493 91 138 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 138 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 90 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 138 235 (accept_3_3 89 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 138 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 88 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 138 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 138 235 (accept_3_3 86 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 138 235
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 84 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 138 235 (accept_3_3 83 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 138 235 (Polychromatic418967fa.accept_10_2_8_5_1_587 82 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 235 (accept_3_3 80 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 138 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 138 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 78 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 138 235 (accept_3_3 77 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 138 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 138 235 (Polychromatic418967fa.accept_18_3_12_1_1_3787 75 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 235 (accept_3_3 74 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 138 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 138 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 72 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 138 235 (accept_3_3 71 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 138 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 235 (accept_3_3 68 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 66 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 138 235 (accept_3_3 65 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 138 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 138 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 235 (accept_3_3 62 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 235 (accept_3_3 59 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 235 (accept_3_3 56 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 235
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 54 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 235 (accept_3_3 53 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 235 (accept_3_3 50 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 138 235 (accept_3_3 47 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 138 235 (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 235 (accept_3_3 44 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 235 (accept_3_3 41 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 235 (Polychromatic418967fa.accept_15_9_3_10_1_2312 39 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 235 (accept_3_3 38 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 235
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 235 (accept_3_3 35 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 235 (accept_3_3 32 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 235
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 235 (accept_3_3 29 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 235 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 138 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 235 (accept_3_3 26 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 235 (accept_3_3 23 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 235 (accept_3_3 20 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 235 (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 235
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 235 (accept_3_3 17 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 235 (accept_3_3 14 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 235
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 138 235 (accept_3_3 11 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 138 235 (Polychromatic418967fa.accept_19_10_5_7_1_10007 10 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 235 (accept_3_3 8 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 235
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 235 (accept_3_3 5 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 138 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 235 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 235 (accept_3_3 2 138 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  137 235 (Eq.refl Bool.true) (allA_of_3_1 99 137 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 136 235
  (Eq.refl Bool.true) (allA_succ_of_accept 99 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 136 235 (accept_3_3 98 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 136 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 136 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 136 235
  (Polychromatic418967fa.accept_13_5_6_1_1_822 96 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 136 235 (accept_3_3 95 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 136 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 94 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 136 235 (accept_3_3 92 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 136 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 136 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 90 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 136 235 (accept_3_3 89 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 136 235 (Polychromatic418967fa.accept_15_13_1_10_1_816 88 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 136 235 (accept_3_3 86 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 136 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 136 235
  (Polychromatic418967fa.accept_10_4_6_5_1_74 84 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 136 235 (accept_3_3 83 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 136 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 136 235 (accept_3_3 80 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 136 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 136 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 136 235 (accept_3_3 77 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 136 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 136 235 (accept_3_3 74 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 136 235 (Polychromatic418967fa.accept_13_8_6_1_1_3808 73 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 136 235
  (Polychromatic418967fa.accept_13_7_6_1_1_368 72 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 136 235 (accept_3_3 71 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 136 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 235 (accept_3_3 68 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 136 235 (Polychromatic418967fa.accept_13_2_6_1_1_3807 67 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 235
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 66 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 136 235 (accept_3_3 65 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 136 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 235 (accept_3_3 62 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 136 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 61 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 235
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 136 235 (accept_3_3 59 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 235 (accept_3_3 56 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 235
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 136 235 (accept_3_3 53 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 235 (accept_3_3 50 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 235 (accept_3_3 47 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 235 (accept_3_3 44 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 235
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 235 (accept_3_3 41 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 235 (Polychromatic418967fa.accept_21_19_10_4_1_14102 40 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 235 (accept_3_3 38 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 235 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 136
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 235 (accept_3_3 35 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 235 (accept_3_3 32 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 235
  (Polychromatic418967fa.accept_20_10_16_15_1_1536 30 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 136 235 (accept_3_3 29 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 136 235 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 136 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 235 (accept_3_3 26 136 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 235
  (Polychromatic418967fa.accept_19_6_3_7_1_11437 25 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 136 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 136 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 235 (accept_3_3 23 136 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 136 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 21
  136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 235 (accept_3_3 20
  136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 235
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 136 235 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 136 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 235 (accept_3_3 17 136 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 136 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 235 (accept_3_3 14 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 235 (Polychromatic418967fa.accept_16_12_8_11_1_2695 12 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 235 (accept_3_3 11 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 235 (accept_3_3 8 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 235 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 235 (accept_3_3 5 136 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 136 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 235 (accept_3_3 2 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 135 235 (Eq.refl Bool.true) (allA_succ_of_gcd 100 135 235 5 20 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 135 235 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  99 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 235 (accept_3_3 98
  135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 97 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 96 135 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 96 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 135 235 5 19 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 94
  135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 93 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 135 235 (accept_3_3 92 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 135 235 (Polychromatic418967fa.accept_28_7_23_11_1_10128 91 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 90 135 235 5 18 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 135 235 (accept_3_3 89 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 235 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  87 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 235 (accept_3_3 86
  135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 135 235 5 17 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 135 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 135 235 (accept_3_3 83 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 81 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 135 235 5 16 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 135 235
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 79 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 135 235 (Polychromatic418967fa.accept_18_6_9_1_1_3769 78 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 235 (accept_3_3 77 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 135 235 5 15 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 135 235 (accept_3_3 74
  135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 235
  (Polychromatic418967fa.accept_11_7_3_4_1_729 73 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 135 235 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 235 (accept_3_3 71 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 135 235 5 14 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 135 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 235 (accept_3_3 68 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 235 (Polychromatic418967fa.accept_16_3_7_11_1_1723 67 135
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 235
  (Polychromatic418967fa.accept_16_2_7_11_1_1698 66 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 135 235 5 13 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 235
  (Polychromatic418967fa.accept_16_15_7_11_1_3760 63 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 235 (accept_3_3 62 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 235 5 12 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 235 (accept_3_3 59 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 235
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 235 (accept_3_3 56 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  135 235 5 11 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 135 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 235 (accept_3_3 53 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 235 (Polychromatic418967fa.accept_11_7_3_4_1_729
  51 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 135 235 5 10 27 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 135 235
  (Polychromatic418967fa.accept_17_15_16_14_1_4291 49 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 135 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 235 (accept_3_3 47 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 235 5 9 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 235 (accept_3_3 44 135 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 235 (Polychromatic418967fa.accept_13_4_5_1_1_833
  43 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 235
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 42 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 235 (accept_3_3 41 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  135 235 5 8 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 135 235 (Polychromatic418967fa.accept_18_3_9_1_1_3690 39 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 235 (accept_3_3 38 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 235 (Polychromatic418967fa.accept_16_5_7_11_1_2664 37 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 135 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 135 235 5 7 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 34 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 235 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 235 (accept_3_3 32 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 135 235 (Polychromatic418967fa.accept_16_15_7_11_1_3760 31 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 235 5 6 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 235 (accept_3_3 29 135 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 235
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 235 (accept_3_3 26 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  135 235 5 5 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 135 235 (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 235 (accept_3_3 23 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 21 135
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 135 235 5 4 27 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 135 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 235 (accept_3_3 17 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 235 5 3 27 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 235 (accept_3_3 14 135 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 135 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 235
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 235 (accept_3_3 11 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  135 235 5 2 27 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 135 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 235 (accept_3_3 8 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 235 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 235 5 1 27 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 135 235 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 235 (accept_3_3 2 135 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 135 235 (Polychromatic418967fa.accept_19_1_2_7_1_2054 1 135 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 134 235 (Eq.refl Bool.true) (allA_of_3_1 102 134 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 133
  235 (Eq.refl Bool.true) (allA_succ_of_accept 102 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 133 235 (accept_3_3 101 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 133 235
  (Polychromatic418967fa.accept_21_16_7_4_1_3448 100 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 133 235 (Polychromatic418967fa.accept_22_11_1_15_1_11044 99 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 133 235 (accept_3_3 98 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 133 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 97 133
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 133 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 96 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 133 235 (accept_3_3 95 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 133 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 93 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 133 235 (accept_3_3 92 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 133 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 91 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 133 235 (accept_3_3 89 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 133 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 88 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 133 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 87 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 235 (accept_3_3 86 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 133 235 (accept_3_3 83 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 133 235 (Polychromatic418967fa.accept_21_18_7_4_1_8131 81 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 235 (accept_3_3 80 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 133 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 133
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 133 235 (accept_3_3 77 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 133 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 235 (accept_3_3 74 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 235 (Polychromatic418967fa.accept_14_3_7_11_1_765 73 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 235
  (Polychromatic418967fa.accept_10_2_3_5_1_996 72 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 133 235 (accept_3_3 71 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 133 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 235 (accept_3_3 68 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 133 235 (accept_3_3 65 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 235 (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 133 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 63 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 235 (accept_3_3 62 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 133
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 235 (accept_3_3 59 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 235 (accept_3_3 56 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 235 (Polychromatic418967fa.accept_16_7_5_11_1_4777 55 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 235 (accept_3_3 53 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 235 (accept_3_3 50 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 235 (accept_3_3 47 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 235 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 235 (accept_3_3 44 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 235 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 133
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 235 (accept_3_3 41 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 235 (accept_3_3 38 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 235
  (Polychromatic418967fa.accept_22_14_1_15_1_6055 36 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 133 235 (accept_3_3 35 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 235 (accept_3_3 32 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379
  31 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 235 (accept_3_3 29 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 235 (accept_3_3 26 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 235 (Polychromatic418967fa.accept_16_9_5_11_1_3776 25 133
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 235
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 235 (accept_3_3 23 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 235 (accept_3_3 20 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 235 (Polychromatic418967fa.accept_11_8_1_4_1_2318 19 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 235 (accept_3_3 17 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 235 (accept_3_3 14 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 235
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 235 (accept_3_3 11 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 235 (Polychromatic418967fa.accept_16_9_5_11_1_3776 9 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 235 (accept_3_3 8 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 133 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 235 (accept_3_3 5 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 133 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 235 (accept_3_3 2 133 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 235 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 133 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 132 235 (Eq.refl Bool.true) (allA_succ_of_accept 103 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 103 132
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 132 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 132 235 (accept_3_3 101 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 100 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 132 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 99 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 132 235 (accept_3_3 98 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 132 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 132 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 96 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 132 235 (accept_3_3 95 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 94 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 132 235 (accept_3_3 92 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 132 235 (Polychromatic418967fa.accept_19_15_18_7_1_10018 91 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 132 235
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 90 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 132 235 (accept_3_3 89 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 132 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 88 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 235 (accept_3_3 86 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 85 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 132 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 132 235 (accept_3_3 83 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 82 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 132 235 (Polychromatic418967fa.accept_13_3_2_1_1_2907 81 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 235 (accept_3_3 80 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 79 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 132 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 78 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 132 235 (accept_3_3 77 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 235 (accept_3_3 74 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 73 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 132 235 (accept_3_3 71 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 132 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 132 235 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 235 (accept_3_3 68 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 132 235 (accept_3_3 65 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 132 235 (Polychromatic418967fa.accept_13_12_2_1_1_2909 64 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 132 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 235 (accept_3_3 62 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 235
  (Polychromatic418967fa.accept_16_12_4_11_1_3710 60 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 132 235 (accept_3_3 59 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 132 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 235 (accept_3_3 56 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 235 (Polychromatic418967fa.accept_8_7_4_3_1_156
  55 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 132 235 (accept_3_3 53 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 235 (accept_3_3 50 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 235 (accept_3_3 47 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 132 235 (Polychromatic418967fa.accept_19_8_18_7_1_3143 46 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 235 (accept_3_3 44 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 235
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 42 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 235 (accept_3_3 41 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 235 (accept_3_3 38 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 235
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 235 (accept_3_3 35 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 132 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 132 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 235 (accept_3_3 32 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 235
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 235 (accept_3_3 29 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 132 235 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 235 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 235 (accept_3_3 26 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 132 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 235
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 132 235 (accept_3_3 23 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 132 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 235 (accept_3_3 20 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 235 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 235
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 235 (accept_3_3 17 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 235 (accept_3_3 14 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 235
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 235 (accept_3_3 11 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 235 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 235 (accept_3_3 8 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 235
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 235 (accept_3_3 5 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 132 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 235 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 235 (accept_3_3 2 132 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 235 (Polychromatic418967fa.accept_17_1_13_14_1_478 1 132 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 105 131 235 (Eq.refl Bool.true) (allA_of_3_1 105 131 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 106 130 235 (Eq.refl Bool.true) (allA_succ_of_gcd 105 130 235 5 21 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 104 130 235 (accept_3_3 104 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 130 235 (Polychromatic418967fa.accept_16_7_2_11_1_931 103 130
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 130 235
  (Polychromatic418967fa.accept_9_3_4_1_1_22 102 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 130 235 (accept_3_3 101 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  100 130 235 5 20 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 99 130 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 130 235 (accept_3_3 98 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 130 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 130 235 (Polychromatic418967fa.accept_9_6_4_1_1_390
  96 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 95 130 235 5 19 26 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 130 235
  (Polychromatic418967fa.accept_20_14_10_15_1_3952 94 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 130 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 130 235 (accept_3_3 92 130 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 130 235 (Polychromatic418967fa.accept_14_7_4_11_1_3038 91 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 130 235 5 18 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 130 235 (accept_3_3 89
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 130 235
  (Polychromatic418967fa.accept_9_7_4_1_1_391 88 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 130 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 130 235 (accept_3_3 86 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 85 130 235 5 17 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 84 130 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 84 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 130 235 (accept_3_3 83 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 130 235 (Polychromatic418967fa.accept_19_6_16_7_1_11433 82 130
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 130 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 130 235 5 16 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 130 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 130 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 130 235 (Polychromatic418967fa.accept_9_6_4_1_1_390
  78 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 130 235 (accept_3_3 77
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 130 235
  (Polychromatic418967fa.accept_12_4_10_7_1_149 76 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 130 235 5 15 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 130 235 (accept_3_3 74 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 235 (Polychromatic418967fa.accept_20_12_10_15_1_9869 72
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 130 235 (accept_3_3 71
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 130 235 5 14 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 130 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 130 235 (accept_3_3 68 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 130 235 (Polychromatic418967fa.accept_17_16_11_14_1_4213 67 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 130 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 66 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 130 235 5 13 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 130 235
  (Polychromatic418967fa.accept_12_4_10_7_1_149 64 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 130 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 235 (accept_3_3 62 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 235 5 12 26 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 235 (accept_3_3 59 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 235 (Polychromatic418967fa.accept_20_18_10_15_1_3937 58
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 235 (accept_3_3 56 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  130 235 5 11 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 130 235 (Polychromatic418967fa.accept_16_6_2_11_1_7132 54 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 235 (accept_3_3 53 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 130 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 130 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 51
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 235 5 10 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 130 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 235 (accept_3_3 47 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 130 235 (Polychromatic418967fa.accept_11_2_9_4_1_310 46 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 130 235 5 9 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 130 235 (accept_3_3 44 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 235 (Polychromatic418967fa.accept_9_7_4_1_1_391
  43 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 235 (accept_3_3 41 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  130 235 5 8 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 130 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 130 235 (accept_3_3 38 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 130
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 130 235 5 7 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 130 235
  (Polychromatic418967fa.accept_9_7_4_1_1_391 34 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 235 (accept_3_3 32 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 130 235 (Polychromatic418967fa.accept_19_12_16_7_1_4456 31 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 235 5 6 26 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 235 (accept_3_3 29 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 235 (Polychromatic418967fa.accept_12_4_10_7_1_149
  28 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 235 (accept_3_3 26 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  130 235 5 5 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 130 235 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 130 235 (accept_3_3 23 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 130 235 (Polychromatic418967fa.accept_14_8_4_11_1_3035 22 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 235 5 4 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 235
  (Polychromatic418967fa.accept_20_19_10_15_1_1529 19 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 235 (Polychromatic418967fa.accept_20_18_10_15_1_3937 18 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 235 (accept_3_3 17 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 130 235 5 3 26 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 130 235 (accept_3_3 14
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 130 235 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 235 (accept_3_3 11 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 130 235 5 2 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 235 (accept_3_3 8 130 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 235 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 235
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 130 235 5 1 26 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 130 235 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 235 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 235 (accept_3_3 2 130 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  130 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 129 235 (Eq.refl Bool.true) (allA_succ_of_accept 106 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 106 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 129 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 105 129 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 235 (accept_3_3 104 129 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 129 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 103 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 102 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 129 235 (accept_3_3 101 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 129 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 99 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 235 (accept_3_3 98 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 97 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 96 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 129 235 (accept_3_3 95 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 129 235 (Polychromatic418967fa.accept_13_2_12_1_1_343 93 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 235 (accept_3_3 92 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 91 129 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 90 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 129 235 (accept_3_3 89 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 129 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 235 (accept_3_3 86 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 85 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 235
  (Polychromatic418967fa.accept_10_4_9_5_1_84 84 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 235 (accept_3_3 83 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 81 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 235 (accept_3_3 80 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 235 (accept_3_3 77 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 75 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 235 (accept_3_3 74 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 235 (Polychromatic418967fa.accept_11_7_8_4_1_718 73 129
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 235
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 235 (accept_3_3 71 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 129 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 129 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 235 (accept_3_3 68 129 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 235 (Polychromatic418967fa.accept_9_4_3_1_1_154
  67 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 235 (accept_3_3 65 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 63 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 235 (accept_3_3 62 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 129 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 235 (accept_3_3 59 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 235 (accept_3_3 56 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 235 (accept_3_3 53 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 235 (accept_3_3 50 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 235
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 235 (accept_3_3 47 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 235 (Polychromatic418967fa.accept_11_1_8_4_1_717 45 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 235 (accept_3_3 44 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 129 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 235 (accept_3_3 41 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 235 (accept_3_3 38 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 235 (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 129
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 235
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 235 (accept_3_3 35 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 235 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 235 (accept_3_3 32 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 235 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 235 (accept_3_3 29 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 235 (accept_3_3 26 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 235
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 235 (accept_3_3 23 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 235 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 235 (accept_3_3 20 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 235 (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 129 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 235 (accept_3_3 17 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 235 (accept_3_3 14 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 235 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 235
  (Polychromatic418967fa.accept_11_1_8_4_1_717 12 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 235 (accept_3_3 11 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 235 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 235 (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 235 (accept_3_3 8 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 235 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 235
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 235 (accept_3_3 5 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 235 (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 235 (accept_3_3 2 129 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 235 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 129 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 108 128 235 (Eq.refl Bool.true) (allA_of_3_1 108 128 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 109 127 235 (Eq.refl Bool.true) (allA_succ_of_accept 108 127 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 108 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 127 235 (accept_3_3 107 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 127 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 106 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 127 235 (Polychromatic418967fa.accept_20_5_7_15_1_2668 105 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 127 235 (accept_3_3 104 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 103 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 127 235
  (Polychromatic418967fa.accept_10_2_7_5_1_605 102 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 127 235 (accept_3_3 101 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 127 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 100 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 127 235 (Polychromatic418967fa.accept_16_3_15_11_1_2676 99 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 127 235 (accept_3_3 98 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 127 235 (Polychromatic418967fa.accept_16_1_15_11_1_356 97 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 127 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 96 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 127 235 (accept_3_3 95 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 94 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 127 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 93 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 235 (accept_3_3 92 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 235
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 90 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 127 235 (accept_3_3 89 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 127 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 88 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 235 (accept_3_3 86 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 235 (Polychromatic418967fa.accept_19_9_13_7_1_5830 85 127 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 84 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 235 (accept_3_3 83 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 235 (Polychromatic418967fa.accept_16_1_15_11_1_356 81 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 235 (accept_3_3 80 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 235 (Polychromatic418967fa.accept_11_2_6_4_1_3028 79 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 235
  (Polychromatic418967fa.accept_10_8_7_5_1_602 78 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 235 (accept_3_3 77 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 76 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 235 (accept_3_3 74 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 73 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 235
  (Polychromatic418967fa.accept_10_2_7_5_1_605 72 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 127 235 (accept_3_3 71 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 235 (Polychromatic418967fa.accept_20_10_7_15_1_14113 70 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 235 (Polychromatic418967fa.accept_13_4_10_1_1_1390 69 127 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 235 (accept_3_3 68 127 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 235
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 67 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 235 (accept_3_3 65 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 64 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 235
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 235 (accept_3_3 62 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 61 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 235 (accept_3_3 59 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 58 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 235
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 57 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 235 (accept_3_3 56 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 235 (Polychromatic418967fa.accept_16_7_15_11_1_951 55 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 235 (accept_3_3 53 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 235
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 51 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 127 235 (accept_3_3 50 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 127 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 127 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 235 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 235 (accept_3_3 47 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 235
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 46 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 127 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 235 (accept_3_3 44 127 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 127 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 235
  (Polychromatic418967fa.accept_10_2_7_5_1_605 42 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 235 (accept_3_3 41 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 235 (Polychromatic418967fa.accept_16_7_15_11_1_951 39 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 235 (accept_3_3 38 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 235 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 235
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 235 (accept_3_3 35 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 235 (Polychromatic418967fa.accept_15_4_7_10_1_807 34 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 235 (accept_3_3 32 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 235
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 235 (accept_3_3 29 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 235 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 235 (accept_3_3 26 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 235 (Polychromatic418967fa.accept_19_6_13_7_1_4464 25 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 235
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 235 (accept_3_3 23 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 235 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 235 (Polychromatic418967fa.accept_19_2_13_7_1_7211 21 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 235 (accept_3_3 20 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 235 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 127 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 235
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 235 (accept_3_3 17 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 235 (Polychromatic418967fa.accept_19_15_13_7_1_7246 15 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 235 (accept_3_3 14 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 235 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 235
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 235 (accept_3_3 11 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 235 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 235 (accept_3_3 8 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 235 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 127
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 235
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 235 (accept_3_3 5 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 235 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 127 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 235 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 235 (accept_3_3 2 127 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 235 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 127 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 126 235 (Eq.refl Bool.true) (allA_succ_of_accept 109 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9
  109 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 126 235
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 108 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 126 235 (accept_3_3 107 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 126 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 106 126 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 126 235 (accept_3_3 104 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 235
  (Polychromatic418967fa.accept_19_8_12_7_1_11458 103 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 126 235 (Polychromatic418967fa.accept_13_11_9_1_1_1407 102 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 126 235 (accept_3_3 101 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 126 235 (Polychromatic418967fa.accept_19_5_12_7_1_4416 100
  126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 126 235
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 99 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 126 235 (accept_3_3 98 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 126 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 96 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 126 235 (accept_3_3 95 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 94 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 93 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 126 235 (accept_3_3 92 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 126 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 91 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 126 235 (Polychromatic418967fa.accept_19_14_12_7_1_10027 90 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 235 (accept_3_3 89 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 235 (Polychromatic418967fa.accept_13_10_9_1_1_5609 88 126
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 235
  (Polychromatic418967fa.accept_11_10_5_4_1_711 87 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 126 235 (accept_3_3 86 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 126 235 (accept_3_3 83 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 235 (Polychromatic418967fa.accept_25_7_1_10_1_14111 82 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 126 235 (accept_3_3 80 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 126 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 79 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 126 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 78 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 126 235 (accept_3_3 77 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 76 126
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 235
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 75 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 126 235 (accept_3_3 74 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 126 235 (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 235 (accept_3_3 71 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 235 (Polychromatic418967fa.accept_13_5_9_1_1_1405 70 126
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 126 235 (accept_3_3 68 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 126 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 67 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 126 235 (Polychromatic418967fa.accept_24_18_6_19_1_14112 66 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 235 (accept_3_3 65 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 64 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 235
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 126 235 (accept_3_3 62 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 126 235 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 235 (accept_3_3 59 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 235 (Polychromatic418967fa.accept_13_6_9_1_1_5604 58 126
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 126 235 (accept_3_3 56 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 126 235 (Polychromatic418967fa.accept_17_4_7_14_1_10583 55 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 235 (accept_3_3 53 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 235 (Polychromatic418967fa.accept_19_14_12_7_1_10027 52 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 235
  (Polychromatic418967fa.accept_10_1_6_5_1_304 51 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 126 235 (accept_3_3 50 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 126 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 235 (accept_3_3 47 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 126
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 126 235 (accept_3_3 44 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 126 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 43 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 126 235 (Polychromatic418967fa.accept_15_12_6_10_1_1516 42 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 235 (accept_3_3 41 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 235 (Polychromatic418967fa.accept_17_6_7_14_1_6704 40 126
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 235
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 126 235 (accept_3_3 38 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 126 235 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 235 (accept_3_3 35 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 126 235 (accept_3_3 32 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 126 235 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 126 235 (Polychromatic418967fa.accept_19_11_12_7_1_3188 30 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 235 (accept_3_3 29 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 235
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 126 235 (accept_3_3 26 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 235 (accept_3_3 23 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 235
  (Polychromatic418967fa.accept_19_3_12_7_1_10004 22 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 235 (accept_3_3 20 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 235 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 235
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 235 (accept_3_3 17 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 126 235 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 126 235 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 235 (accept_3_3 14 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 235
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 235 (accept_3_3 11 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 235 (Polychromatic418967fa.accept_11_10_5_4_1_711 10 126 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 235 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 235 (accept_3_3 8 126 235
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 235
  (Polychromatic418967fa.accept_25_7_1_10_1_14111 7 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 126 235 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 126 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 235 (accept_3_3 5 126 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 126 235 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 126 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 235 (Polychromatic418967fa.accept_15_3_6_10_1_1539
  3 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 235 (accept_3_3 2
  126 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 235
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 111 125 235 (Eq.refl Bool.true) (allA_of_3_1 111 125 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 112 124 235 (Eq.refl Bool.true) (allA_succ_of_accept 111 124 235 (Polychromatic418967fa.accept_6_3_4_1_1_8
  111 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 124 235 (accept_3_3
  110 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 124 235
  (Polychromatic418967fa.accept_10_9_4_5_1_616 109 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 124 235 (Polychromatic418967fa.accept_23_16_9_5_1_14110 108 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 124 235 (accept_3_3 107 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 106 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 106 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 105 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 124 235 (accept_3_3 104 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  103 124 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 103 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 124 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 102 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 124 235 (accept_3_3 101 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 100 124
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 99 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 124 235 (accept_3_3 98 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  97 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 97 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 124 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 96 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 124 235 (accept_3_3 95 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 94 124 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 94 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 93 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 124 235 (accept_3_3 92 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 124 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 91 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 90 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 124 235 (accept_3_3 89 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 124 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 88 124 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 87 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 124 235 (accept_3_3 86 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 85 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 124 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 84 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 235 (accept_3_3 83 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 124 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 81 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 124 235 (accept_3_3 80 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 79 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 124 235 (accept_3_3 77 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 76 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 124 235 (accept_3_3 74 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 124 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 73 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 124 235 (accept_3_3 71 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 124 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 124 235 (accept_3_3 68 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 124 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 124 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 124 235 (accept_3_3 65 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 124 235 (accept_3_3 62 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 124 235 (Polychromatic418967fa.accept_10_1_4_5_1_1031 61 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 124 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 124 235 (accept_3_3 59 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 124 235 (accept_3_3 56 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 124 235 (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 235 (accept_3_3 53 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 124 235 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 124
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 124 235 (accept_3_3 50 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 124 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 235 (accept_3_3 47 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 124 235 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 124 235 (accept_3_3 44 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 124 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 235 (accept_3_3 41 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 124 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 235 (accept_3_3 38 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 235 (accept_3_3 35 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 235 (accept_3_3 32 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 31 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 235 (accept_3_3 29 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 235 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 124 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 235 (accept_3_3 26 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 235 (Polychromatic418967fa.accept_18_7_16_1_1_4951 25 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 235 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 235 (accept_3_3 23 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 235 (accept_3_3 20 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 235 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 235 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 235 (accept_3_3 17 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 235 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 124 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 235 (accept_3_3 14 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 235 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 235 (accept_3_3 11 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 235 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 235 (accept_3_3 8 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 235 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 235 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 235 (accept_3_3 5 124 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 235 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 124 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 235
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 235 (accept_3_3 2 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 235 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 124 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  235))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 123 235 (Eq.refl Bool.true) (allA_succ_of_accept 112 123 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 112 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 111 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 111 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 235 (accept_3_3 110 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 123 235 (Polychromatic418967fa.accept_13_5_6_1_1_822 109 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 235
  (Polychromatic418967fa.accept_10_8_3_5_1_613 108 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 123 235 (accept_3_3 107 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  106 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 106 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 123 235 (Polychromatic418967fa.accept_11_6_2_4_1_1703 105 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 235 (accept_3_3 104 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 103 123
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 102 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 123 235 (accept_3_3 101 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 100 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 123 235 (Polychromatic418967fa.accept_13_8_6_1_1_3808 99 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 235 (accept_3_3 98 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 97 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 235
  (Polychromatic418967fa.accept_13_5_6_1_1_822 96 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 123 235 (accept_3_3 95 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 94 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 235 (accept_3_3 92 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 235 (Polychromatic418967fa.accept_21_7_18_4_1_5024 91 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 235
  (Polychromatic418967fa.accept_20_10_3_15_1_1546 90 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 123 235 (accept_3_3 89 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 87 123
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 235 (accept_3_3 86 123
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 85 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 235 (accept_3_3 83 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 235 (Polychromatic418967fa.accept_12_9_3_7_1_924
  81 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 235 (accept_3_3 80
  123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 235
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 123 235 (Polychromatic418967fa.accept_10_8_3_5_1_613 78 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 235 (accept_3_3 77 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 75
  123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 235 (accept_3_3 74
  123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 235
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 73 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 123 235 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 235 (accept_3_3 71 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 235 (Polychromatic418967fa.accept_12_9_3_7_1_924
  69 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 235 (accept_3_3 68
  123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 235
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 235 (accept_3_3 65 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 235
  (Polychromatic418967fa.accept_25_13_23_10_1_14109 63 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 235 (accept_3_3 62 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 235 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 123
  235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 235 (accept_3_3 59 123
  235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 235
  (Polychromatic418967fa.accept_6_4_3_1_1_57 58 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 235 (accept_3_3 56 123 235 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 123 235 (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 235
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 54 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 123 235 (accept_3_3 53 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 123 235 (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 235 (accept_3_3 50 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 123 235 (accept_3_3 47 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 123 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 45 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 235 (accept_3_3 44 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 235
  (Polychromatic418967fa.accept_10_2_3_5_1_996 42 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 123 235 (accept_3_3 41 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 235 (accept_3_3 38 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 235
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 123 235 (accept_3_3 35 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 123 235 (Polychromatic418967fa.accept_12_9_3_7_1_924 33 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 235 (accept_3_3 32 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 123 235 (accept_3_3 29 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 123 235 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 235 (accept_3_3 26 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 235
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 235 (accept_3_3 23 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 235 (accept_3_3 20 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 235 (Polychromatic418967fa.accept_21_19_18_4_1_4977 19 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 235
  (Polychromatic418967fa.accept_10_8_3_5_1_613 18 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 235 (accept_3_3 17 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 235 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 235 (accept_3_3 14 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 235 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 123 235
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 235
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 235 (accept_3_3 11 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 235 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 235 (accept_3_3 8 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 235 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 235
  (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 235 (accept_3_3 5 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 235 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 235 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 235 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 235 (accept_3_3 2 123 235 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 235 (Polychromatic418967fa.accept_17_1_4_14_1_8058 1 123 235 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  235)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_235_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


