-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch234
-- name    : Polychromatic418967fa_Branch234
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:32.99753+00:00
-- url     : https://prove2.me/theorems/2e25eae2-abb3-4436-8cbe-696cbcb48df5
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch234_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_234 : allB 234 234 :=
  allB_succ' 2 233 234 (Eq.refl Bool.true) (allA_succ_of_accept 1 233 234 (accept_3_4 1 233 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 234)) (allB_succ' 3 232 234 (Eq.refl Bool.true) (allA_succ_of_gcd 2 232 234 2 1 116
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 234
  (Polychromatic418967fa.accept_15_1_7_9_1_20 1 232 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 234))) (allB_succ' 4 231 234 (Eq.refl Bool.true) (allA_succ_of_gcd 3 231 234 3 1 77 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 231 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 231 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 231 234)))) (allB_succ' 5 230 234 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  230 234 2 2 115 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 230 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 230 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 230 234 2 1 115 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 230 234 (accept_3_4 1 230 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 234))))) (allB_succ' 6 229 234 (Eq.refl Bool.true) (allA_succ_of_accept 5 229 234
  (accept_3_5 5 229 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 234
  (Polychromatic418967fa.accept_17_4_8_13_1_7960 4 229 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 229 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 229 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 234 (accept_3_5 2 229 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 229 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 229 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 234)))))) (allB_succ' 7 228 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 228 234 6 1 38 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 228 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 228 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 234 2 2 114 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 234 3 1 76 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 234 2 1 114 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 228 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 234))))))) (allB_succ' 8 227 234 (Eq.refl Bool.true) (allA_succ_of_accept 7 227 234 (accept_3_4 7 227
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 234
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 227 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 227 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 234 (accept_3_4 4 227 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 227 234 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 227 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  227 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 234 (accept_3_4 1 227
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227 234)))))))) (allB_succ' 9 226 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 226 234 2 4 113 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 226 234 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 226 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 226 234 2 3 113 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 226 234 (accept_3_5 5 226 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 226 234 2 2 113 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 226 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3
  226 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 234 2 1 113 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 226 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 234))))))))) (allB_succ' 10 225 234 (Eq.refl Bool.true) (allA_succ_of_gcd 9 225 234 9 1 25 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 234
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 225 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 225 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 234 3 2 75 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 225 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 225 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 225 234 3 1 75 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 225 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 225 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 225 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 234)))))))))) (allB_succ' 11 224 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 224 234 2 5 112 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 224 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 234 2 4 112 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 224 234 (accept_3_4 7
  224 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224 234 2 3 112 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 234
  (Polychromatic418967fa.accept_15_5_14_9_1_274 5 224 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 224 234 2 2 112 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 224 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 224 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 234 2 1 112 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 234 (accept_3_4 1 224 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 224 234))))))))))) (allB_succ' 12 223 234 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 223 234 (accept_3_5 11 223 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 234 (Polychromatic418967fa.accept_19_10_14_6_1_5819 10 223 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 223 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 234 (accept_3_5 8 223 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 223 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 234
  (Polychromatic418967fa.accept_17_6_2_13_1_3051 6 223 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 234 (accept_3_5 5 223 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 223 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 234 (Polychromatic418967fa.accept_14_3_13_10_1_761 3 223 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 234 (accept_3_5 2 223 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 223 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 234)))))))))))) (allB_succ' 13 222 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 222 234 6 2 37 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 222 234 (Polychromatic418967fa.accept_19_11_13_6_1_5817 11 222 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 234 2 5 111 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 222 234 3 3 74 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 222 234 2 4 111 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 222 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 234 6 1 37 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 234 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 222 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 234 2 2 111 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 222 234 3 1 74 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 222 234 2 1 111 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 222 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 234))))))))))))) (allB_succ' 14 221 234 (Eq.refl Bool.true) (allA_succ_of_gcd 13 221 234 13 1 17 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 221 234
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 221 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 221 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 234 (accept_3_4 10 221 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 234 (Polychromatic418967fa.accept_22_9_1_14_1_4463 9 221 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 221 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 234 (accept_3_4 7 221 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 221 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 221 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 234 (accept_3_4 4 221 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 234
  (Polychromatic418967fa.accept_11_2_1_3_1_683 2 221 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 234 (accept_3_4 1 221 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  234)))))))))))))) (allB_succ' 15 220 234 (Eq.refl Bool.true) (allA_succ_of_gcd 14 220 234 2 7 110 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 234
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 220 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 220 234 2 6 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 220 234 (accept_3_5 11 220 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 220 234 2 5 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 220 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 220 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 234 2 4 110 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 234
  (Polychromatic418967fa.accept_21_7_10_3_1_1049 7 220 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 220 234 2 3 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 220 234 (accept_3_5 5 220 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 220 234 2 2 110 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 220 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 220 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 234 2 1 110 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 234
  (Polychromatic418967fa.accept_15_1_10_9_1_1495 1 220 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 220 234))))))))))))))) (allB_succ' 16 219 234 (Eq.refl Bool.true) (allA_succ_of_gcd 15 219 234 3 5 73 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 219 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 219 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 234 3 4 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 234
  (Polychromatic418967fa.accept_17_11_15_13_1_11717 11 219 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 219 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 219 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 234 3 3 73 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 219 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 219 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 234 3 2 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 234
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 219 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 219 234 3 1 73 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 219 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 219 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 219 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 234)))))))))))))))) (allB_succ' 17 218 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 218 234 2 8 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 218 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 218 234 2 7 109 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 218 234 (accept_3_4 13
  218 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 218 234 2 6 109 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 218 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 218 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 218 234 2 5 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 218 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 218 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 218 234 2 4 109 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 218 234 (accept_3_4 7 218 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 218 234 2 3 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 218 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  218 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 234 2 2 109 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 234
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 218 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 234 2 1 109 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 234 (accept_3_4 1 218 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  234))))))))))))))))) (allB_succ' 18 217 234 (Eq.refl Bool.true) (allA_succ_of_accept 17 217 234 (accept_3_5 17 217 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 234 (Polychromatic418967fa.accept_11_5_8_3_1_66
  16 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 234 (accept_3_5 14 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 234 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 217 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 234 (accept_3_5 11 217 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 234 (Polychromatic418967fa.accept_21_10_7_3_1_4884 10 217
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 234
  (Polychromatic418967fa.accept_21_9_7_3_1_4888 9 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 234 (accept_3_5 8 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 217 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 234 (accept_3_5 5 217 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 234 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 217 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 234 (accept_3_5 2 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 234 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 217 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 234)))))))))))))))))) (allB_succ' 19 216 234 (Eq.refl Bool.true) (allA_succ_of_gcd 18 216
  234 18 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  216 234 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 216 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 216 234 2 8 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 216 234 3 5 72 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 216 234 2 7 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 234 (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 216
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 234 6 2 36 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 216 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 216 234 2 5 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 216 234 9 1 24 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 216 234 2 4 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 216 234 (Polychromatic418967fa.accept_21_7_6_3_1_8072 7 216 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 234 6 1 36 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 216 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 216 234 2 2 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 216 234 3 1 72 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 216 234 2 1 108 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 216 234 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 216 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 234))))))))))))))))))) (allB_succ' 20 215 234
  (Eq.refl Bool.true) (allA_succ_of_accept 19 215 234 (accept_3_4 19 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 215 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 215 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 215 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 234 (accept_3_4 16 215 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 234 (Polychromatic418967fa.accept_7_1_5_3_1_268
  15 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 234
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 215 234 (accept_3_4 13 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 215 234 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 215 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 234 (accept_3_4 10 215 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 234 (accept_3_4 7 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 215 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 234 (accept_3_4 4 215 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 215 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 234 (accept_3_4 1 215 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  234)))))))))))))))))))) (allB_succ' 21 214 234 (Eq.refl Bool.true) (allA_succ_of_gcd 20 214 234 2 10 107 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 234
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 234 2 9 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 234 (accept_3_5 17 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 234 2 8 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 214 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 234 2 7 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 234 2 6 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 234 (accept_3_5 11 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 234 2 5 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 234 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 214 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 234 2 4 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 234
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 234 2 3 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 234 (accept_3_5 5 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 234 2 2 107 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 214 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 234 2 1 107 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 214 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 234))))))))))))))))))))) (allB_succ' 22 213 234 (Eq.refl Bool.true) (allA_succ_of_gcd 21 213 234 3 7 71
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 234
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 213 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 213 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 234 3 6 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 234 (Polychromatic418967fa.accept_10_7_3_4_1_978
  17 213 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 234
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 213 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 213 234 3 5 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 213 234 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 213 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 234 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 213
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 234 3 4 71 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 213 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 234 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 213 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 234 3 3 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 213 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 213 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 213 234 3 2 71 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 213 234 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 213 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 213 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 234 3 1 71 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 234
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 213 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 234 (Polychromatic418967fa.accept_20_1_13_14_1_1481 1 213 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213 234)))))))))))))))))))))) (allB_succ' 23 212 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 212 234 2 11 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 212 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 212 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 212 234 2 10 106 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 212 234 (accept_3_4 19 212 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 212 234 2 9 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 212 234 (Polychromatic418967fa.accept_10_7_2_4_1_569
  17 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 234 2 8 106 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 234 2 7 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 234 (accept_3_4 13 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 234 2 6 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 212 234 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 212 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 234 2 5 106 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 234 2 4 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 212 234 (accept_3_4 7 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 212 234 2 3 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 212 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 212 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 234 2 2 106 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 234 2 1 106 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 234 (accept_3_4 1 212 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  234))))))))))))))))))))))) (allB_succ' 24 211 234 (Eq.refl Bool.true) (allA_succ_of_accept 23 211 234 (accept_3_5 23
  211 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 234
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 22 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 211 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 234 (accept_3_5 20 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 211 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 211 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 234 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 234 (accept_3_5 17
  211 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 211 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 234 (accept_3_5 14 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 211 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 211 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 234 (Polychromatic418967fa.accept_7_5_1_3_1_103
  12 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 234 (accept_3_5 11
  211 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 234
  (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 211 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 234 (accept_3_5 8 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 211 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 211 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 234 (Polychromatic418967fa.accept_15_6_1_9_1_1476
  6 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 234 (accept_3_5 5
  211 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 211 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 211 234 (Polychromatic418967fa.accept_19_3_2_6_1_11398 3 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 234 (accept_3_5 2 211 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 211 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 211 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 234)))))))))))))))))))))))) (allB_succ' 25 210 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 210 234 6 4 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 234 (Polychromatic418967fa.accept_27_23_21_18_1_6228 23 210 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 234 2 11 105 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 210 234 3 7 70 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 234 2 10 105 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 234
  (Polychromatic418967fa.accept_17_2_6_13_1_2056 19 210 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 234 6 3 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 210 234 (Polychromatic418967fa.accept_22_17_12_14_1_9421 17 210 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 234 2 8 105 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 210 234 3 5 70 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 234 2 7 105 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 234
  (Polychromatic418967fa.accept_11_2_1_3_1_683 13 210 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 234 6 2 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 210 234 (Polychromatic418967fa.accept_17_11_6_13_1_10553 11 210 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 234 2 5 105 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 234 3 3 70 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 234 2 4 105 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 234
  (Polychromatic418967fa.accept_17_7_6_13_1_10548 7 210 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 234 6 1 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 210 234 (Polychromatic418967fa.accept_19_5_1_6_1_4361 5 210 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 234 2 2 105 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 234 3 1 70 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 234 2 1 105 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 234
  (Polychromatic418967fa.accept_20_1_10_14_1_1472 1 210 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 234))))))))))))))))))))))))) (allB_succ' 26 209 234 (Eq.refl Bool.true) (allA_succ_of_accept 25 209 234
  (accept_3_4 25 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 234
  (Polychromatic418967fa.accept_20_4_9_14_1_5316 24 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 209 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 209 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 234 (accept_3_4 22 209 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 209 234 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 209 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 234
  (Polychromatic418967fa.accept_15_5_14_9_1_274 20 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 234 (accept_3_4 19 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 234 (Polychromatic418967fa.accept_14_3_13_10_1_761 17 209 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 234 (accept_3_4 16 209 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 234
  (Polychromatic418967fa.accept_23_14_2_4_1_14085 14 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 209 234 (accept_3_4 13 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 209 234 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 209 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 209 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 234 (accept_3_4 10 209 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 234
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 234 (accept_3_4 7 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 234 (Polychromatic418967fa.accept_15_6_14_9_1_1471 6 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 209 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 234 (accept_3_4 4 209 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 234 (accept_3_4 1 209 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  234)))))))))))))))))))))))))) (allB_succ' 27 208 234 (Eq.refl Bool.true) (allA_succ_of_gcd 26 208 234 26 1 8 9
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 208 234
  (Polychromatic418967fa.accept_17_8_4_13_1_3014 25 208 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 208 234 2 12 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 208 234 (accept_3_5 23 208 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 208 234 2 11 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 208 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 208 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 234 2 10 104 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 208 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 208 234 2 9 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 208 234 (accept_3_5 17 208 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 234 2 8 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 208 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 234 2 7 104 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 208 234 13 1 16 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 208 234 2 6 104 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 234 (accept_3_5 11
  208 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 234 2 5 104 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 208 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 208 234 2 4 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 208 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 208 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 234 2 3 104 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 234 (accept_3_5 5 208 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 234 2 2 104 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3
  208 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 234 2 1 104 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 208 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 234))))))))))))))))))))))))))) (allB_succ' 28 207 234 (Eq.refl Bool.true) (allA_succ_of_gcd 27 207 234 9
  3 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 207
  234 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 207 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 207 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 234 3 8 69 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 234
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 207 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 207 234 3 7 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 234
  (Polychromatic418967fa.accept_15_4_12_9_1_773 19 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 207 234 9 2 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 207 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 207 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 234 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 207
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 234 3 5 69 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 207 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 234 3 4 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 234 (Polychromatic418967fa.accept_10_1_7_4_1_968
  11 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 207 234 9 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 207 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 207 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 234 (Polychromatic418967fa.accept_14_7_11_10_1_2155 7 207
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 234 3 2 69 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 234 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 207 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 234 3 1 69 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 207 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 207 234)))))))))))))))))))))))))))) (allB_succ' 29 206 234 (Eq.refl Bool.true) (allA_succ_of_gcd 28 206 234
  2 14 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  206 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 206 234 2 13 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 206 234 (accept_3_4 25 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 234 2 12 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 234 (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 206 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 234 2 11 103 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 234 2 10 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 234 (accept_3_4 19 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 234 2 9 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 206 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 234 2 8 103 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 234 2 7 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 234 (accept_3_4 13 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 234 2 6 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 234 (Polychromatic418967fa.accept_19_11_16_6_1_7155 11 206 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 234 2 5 103 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 234 2 4 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 234 (accept_3_4 7 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 234 2 3 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 206 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 234 2 2 103 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 234
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 234 2 1 103 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 234 (accept_3_4 1 206 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  234))))))))))))))))))))))))))))) (allB_succ' 30 205 234 (Eq.refl Bool.true) (allA_succ_of_accept 29 205 234
  (accept_3_5 29 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 234
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 28 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 234 (accept_3_5 26 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 234 (Polychromatic418967fa.accept_23_2_21_4_1_14084 25 205 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 234
  (Polychromatic418967fa.accept_19_5_15_6_1_1986 24 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 234 (accept_3_5 23 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 205 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 234 (accept_3_5 20 205 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 205 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 234
  (Polychromatic418967fa.accept_15_3_10_9_1_769 18 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 234 (accept_3_5 17 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 234 (accept_3_5 14 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 205 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 234 (accept_3_5 11 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 234 (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 234 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 234 (accept_3_5 8 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 205 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 234 (accept_3_5 5 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 234 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 205 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 234 (accept_3_5 2 205 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 205 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 234)))))))))))))))))))))))))))))) (allB_succ' 31 204
  234 (Eq.refl Bool.true) (allA_succ_of_gcd 30 204 234 6 5 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 234 (Polychromatic418967fa.accept_16_13_12_10_1_3540 29 204
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 234 2 14 102 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 204 234 3 9 68 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 204 234 2 13 102 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 204 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 234 6 4 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 204 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 204 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 234 2 11 102 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 204 234 3 7 68 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 234 2 10 102 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 204 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 234 6 3 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 234 (Polychromatic418967fa.accept_21_17_15_3_1_4937 17 204 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 234 2 8 102 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 204 234 3 5 68 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 204 234 2 7 102 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 234
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 13 204 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 204 234 6 2 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 204 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 204 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 234 2 5 102 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 234 3 3 68 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 234 2 4 102 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 234
  (Polychromatic418967fa.accept_19_7_14_6_1_9987 7 204 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 234 6 1 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 204 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 234 2 2 102 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 234 3 1 68 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 234 2 1 102 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 234
  (Polychromatic418967fa.accept_19_1_14_6_1_1983 1 204 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 234))))))))))))))))))))))))))))))) (allB_succ' 32 203 234 (Eq.refl Bool.true) (allA_succ_of_accept 31
  203 234 (accept_3_4 31 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 234
  (Polychromatic418967fa.accept_11_8_5_3_1_694 30 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 203 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 203 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 234 (accept_3_4 28 203 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 203 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 203 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 234
  (Polychromatic418967fa.accept_17_9_16_13_1_6636 26 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 203 234 (accept_3_4 25 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 203 234 (Polychromatic418967fa.accept_20_4_3_14_1_6813 24 203 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 234 (Polychromatic418967fa.accept_19_4_13_6_1_8671 23 203
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 234 (accept_3_4 22 203
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 234 (Polychromatic418967fa.accept_4_1_3_2_1_3
  21 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 234
  (Polychromatic418967fa.accept_17_3_16_13_1_6635 20 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 203 234 (accept_3_4 19 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 203 234 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 203 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 234 (accept_3_4 16 203 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 234
  (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 234 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 203 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 234 (accept_3_4 13 203 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 234 (Polychromatic418967fa.accept_16_12_11_10_1_1667 12
  203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 234
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 11 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 203 234 (accept_3_4 10 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 203 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 203 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 234 (accept_3_4 7 203 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 234 (Polychromatic418967fa.accept_21_6_14_3_1_4932
  6 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 234 (accept_3_4 4 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 234 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 203 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 234 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2 203 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 234 (accept_3_4 1 203 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 234)))))))))))))))))))))))))))))))) (allB_succ' 33 202 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 202 234 2 16 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 202 234 (Polychromatic418967fa.accept_14_3_6_10_1_752 31 202 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 202 234 2 15 101 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 202 234 (accept_3_5 29 202 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 202 234 2 14 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 202 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 202 234 2 13 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 202 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 202 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 202 234 2 12 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 202 234 (accept_3_5 23 202 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 202 234 2 11 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 202 234 (Polychromatic418967fa.accept_12_9_10_6_1_872
  21 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 234 2 10 101 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 234
  (Polychromatic418967fa.accept_17_2_15_13_1_3034 19 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 202 234 2 9 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 202 234 (accept_3_5 17 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 234 2 8 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 202 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 234 2 7 101 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 234
  (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 234 2 6 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 234 (accept_3_5 11 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 234 2 5 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 202 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 234 2 4 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 234 2 3 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 234 (accept_3_5 5 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 234 2 2 101 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 202 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 234 2 1 101 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 234
  (Polychromatic418967fa.accept_15_1_7_9_1_20 1 202 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 234))))))))))))))))))))))))))))))))) (allB_succ' 34 201 234 (Eq.refl Bool.true) (allA_succ_of_gcd 33 201
  234 3 11 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  201 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 201 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 201 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 201 234 3 10 67 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 201 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 201 234 3 9 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201 234 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 234
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 201 234 3 8 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 201 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 201 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 234 3 7 67 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 234
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 234 3 6 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  17 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 201 234 3 5 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 201 234 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 234 (Polychromatic418967fa.accept_19_13_11_6_1_3128 13 201
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 234 3 4 67 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 234 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 234 3 3 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 201 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 201 234 3 2 67 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 201 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 201 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 234 3 1 67 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 201 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 201 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201 234)))))))))))))))))))))))))))))))))) (allB_succ' 35 200 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 200 234 2 17 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 200 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 33 200 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 234 2 16 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 234 (accept_3_4 31 200 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 234 2 15 100 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 200 234 2 14 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 200 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 200 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 200 234 2 13 100 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 200 234 (accept_3_4 25 200 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 200 234 2 12 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 200 234 (Polychromatic418967fa.accept_11_1_2_3_1_688
  23 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 234 2 11 100 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 234 2 10 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 234 (accept_3_4 19 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 234 2 9 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 234 (Polychromatic418967fa.accept_37_17_15_12_1_14083 17 200 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 234 2 8 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 200 234 2 7 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 200 234 (accept_3_4 13 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 234 2 6 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 200 234 (Polychromatic418967fa.accept_15_11_5_9_1_3205 11 200 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 234 2 5 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 234 2 4 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 200 234 (accept_3_4 7 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 200 234 2 3 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 200 234 (Polychromatic418967fa.accept_27_5_11_18_1_12052 5 200 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 234 2 2 100 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 234 2 1 100 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 234 (accept_3_4 1 200 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  234))))))))))))))))))))))))))))))))))) (allB_succ' 36 199 234 (Eq.refl Bool.true) (allA_succ_of_accept 35 199 234
  (accept_3_5 35 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 234
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 199 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 199 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 234 (accept_3_5 32 199 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 199 234 (Polychromatic418967fa.accept_22_9_1_14_1_4463 31 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 234
  (Polychromatic418967fa.accept_16_14_7_10_1_898 30 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 234 (accept_3_5 29 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 234 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 234 (accept_3_5 26 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 199 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 234
  (Polychromatic418967fa.accept_11_2_1_3_1_683 24 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 234 (accept_3_5 23 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 234 (Polychromatic418967fa.accept_19_3_9_6_1_12696 22 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 199 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 234 (accept_3_5 20 199 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 234 (Polychromatic418967fa.accept_16_3_7_10_1_3503 19 199 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 234
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 234 (accept_3_5 17 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 234 (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 234 (accept_3_5 14 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 199 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 234
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 234 (accept_3_5 11 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 234 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 234 (accept_3_5 8 199 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 234 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 234
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 234 (accept_3_5 5 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 234 (Polychromatic418967fa.accept_20_4_19_14_1_5327 4 199 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 234 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 199 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 234 (accept_3_5 2 199 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 234)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 198 234 (Eq.refl Bool.true) (allA_succ_of_gcd 36 198 234 18 2 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 198 234 (Polychromatic418967fa.accept_15_5_3_9_1_283
  35 198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 234 2 17 99 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 198 234 3 11 66
  78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 234 2 16
  99 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 234
  (Polychromatic418967fa.accept_19_12_8_6_1_8646 31 198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 234 6 5 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 198 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 198 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 234 2 14 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 198 234 9 3 22 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 198 234 2 13 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 234
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 234 6 4 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 198 234 (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 198 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 234 2 11 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 234 3 7 66 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 234 2 10 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 234 18 1 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 234 (Polychromatic418967fa.accept_19_17_8_6_1_7146 17 198 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 234 2 8 99 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 234 3 5 66 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 234 2 7 99 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 234 6 2 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 198 234 (Polychromatic418967fa.accept_24_11_6_18_1_10695 11 198 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 234 2 5 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 234 9 1 22 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 234 2 4 99 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 234
  (Polychromatic418967fa.accept_17_7_11_13_1_2037 7 198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 234 6 1 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 198 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 234 2 2 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 198 234 3 1 66 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 198 234 2 1 99 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  198 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  234))))))))))))))))))))))))))))))))))))) (allB_succ' 38 197 234 (Eq.refl Bool.true) (allA_succ_of_accept 37 197 234
  (accept_3_4 37 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 234
  (Polychromatic418967fa.accept_21_15_8_3_1_8086 36 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 197 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 234 (accept_3_4 34 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 197 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 234 (Polychromatic418967fa.accept_7_4_1_3_1_277
  32 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 234 (accept_3_4 31
  197 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 197 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 234 (accept_3_4 28 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 197 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 234 (Polychromatic418967fa.accept_7_5_1_3_1_103
  26 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 234 (accept_3_4 25
  197 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 234
  (Polychromatic418967fa.accept_19_5_7_6_1_11379 24 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 197 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 234 (accept_3_4 22 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 197 234 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 197 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 234
  (Polychromatic418967fa.accept_17_3_10_13_1_2021 20 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 197 234 (accept_3_4 19 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 197 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 197 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 234 (Polychromatic418967fa.accept_21_17_8_3_1_9576 17 197
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 234 (accept_3_4 16 197
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 197 234 (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 234 (accept_3_4 13 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 197 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 234 (accept_3_4 10 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 234 (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 234 (accept_3_4 7 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 234 (Polychromatic418967fa.accept_21_6_8_3_1_11140 6 197 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 234 (accept_3_4 4 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 234 (accept_3_4 1 197 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 234)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 196 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 196 234 2 19 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 196 234 (Polychromatic418967fa.accept_15_7_1_9_1_1500 37 196 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 196 234 2 18 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 196 234 (accept_3_5 35 196 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 196 234 2 17 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 196 234
  (Polychromatic418967fa.accept_12_9_4_6_1_460 33 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 196 234 2 16 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 196 234 (Polychromatic418967fa.accept_21_10_7_3_1_4884 31 196 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 234 2 15 98 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 234 (accept_3_5 29 196 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 234 2 14 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 234
  (Polychromatic418967fa.accept_12_3_4_6_1_434 27 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 196 234 2 13 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 196 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 196 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 196 234 2 12 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 234 (accept_3_5 23 196 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 234 2 11 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 234 (Polychromatic418967fa.accept_12_9_4_6_1_460
  21 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 234 2 10 98 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 234
  (Polychromatic418967fa.accept_25_19_21_9_1_3265 19 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 196 234 2 9 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 196 234 (accept_3_5 17 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 234 2 8 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 196 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 196 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 234 2 7 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 234
  (Polychromatic418967fa.accept_25_13_21_9_1_14033 13 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 196 234 2 6 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 196 234 (accept_3_5 11 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 196 234 2 5 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 196 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 196 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 234 2 4 98 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 234
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 234 2 3 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 234 (accept_3_5 5 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  234 2 2 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 196 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 234 2 1 98 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 234 (Polychromatic418967fa.accept_21_1_7_3_1_6450 1 196 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 234)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 195 234 (Eq.refl Bool.true) (allA_succ_of_gcd 39 195 234 39 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 195 234
  (Polychromatic418967fa.accept_11_5_8_3_1_66 38 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 195 234 3 12 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 195 234 (Polychromatic418967fa.accept_21_14_6_3_1_3382
  35 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 195 234 3 11 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 195 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 195 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 234 (Polychromatic418967fa.accept_10_1_5_4_1_276
  31 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 234 3 10 65 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 234 3 9 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 195 234 13 2 15 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 195 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 195 234 3 8 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 195 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 195
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 195 234 3 7 65 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 195 234
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 234 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 234 3 6 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 195 234 3 5 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 195 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 195 234 13 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 195 234 3 4 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 11
  195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 195 234 3 3 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 195 234 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 234 (Polychromatic418967fa.accept_16_7_3_10_1_3614 7 195
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 234 3 2 65 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 195 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 234 3 1 65 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 195 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 195 234)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 194 234 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 194 234 2 20 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 194 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 194 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 194 234 2 19 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 194 234 (accept_3_4 37 194 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 194 234 2 18 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 194 234 (Polychromatic418967fa.accept_15_5_14_9_1_274 35 194
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 234 2 17 97 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 234 2 16 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 234 (accept_3_4 31 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 234 2 15 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 194 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 234 2 14 97 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 234
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 234 2 13 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 234 (accept_3_4 25 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 234 2 12 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 194 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 234 2 11 97 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 234
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 234 2 10 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 234 (accept_3_4 19 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 234 2 9 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 234 (Polychromatic418967fa.accept_19_17_4_6_1_5810 17 194 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 234 2 8 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 234 2 7 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 234 (accept_3_4 13 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 234 2 6 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 234 (Polychromatic418967fa.accept_17_11_7_13_1_11667 11 194 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 234 2 5 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 234 2 4 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 234 (accept_3_4 7 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  234 2 3 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 234 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 194 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 234 2 2 97 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 194 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 234 2 1 97 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 234 (accept_3_4 1 194 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 234))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 193
  234 (Eq.refl Bool.true) (allA_succ_of_accept 41 193 234 (accept_3_5 41 193 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 193 234 (Polychromatic418967fa.accept_19_2_3_6_1_4415 40 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 193 234 (accept_3_5 38 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 193 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 193 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 193 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 234 (accept_3_5 35 193 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 234
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 193 234 (accept_3_5 32 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 193 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 193 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 234 (accept_3_5 29 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 234 (Polychromatic418967fa.accept_17_11_6_13_1_10553 28
  193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 234 (accept_3_5 26 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 234 (Polychromatic418967fa.accept_16_9_1_10_1_3610 25 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 234 (Polychromatic418967fa.accept_17_7_6_13_1_10548 24 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 234 (accept_3_5 23 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 193 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 234
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 193 234 (accept_3_5 20 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 193 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 193 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 234 (Polychromatic418967fa.accept_15_3_13_9_1_3196 18 193
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 234 (accept_3_5 17 193
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 234
  (Polychromatic418967fa.accept_19_16_3_6_1_1941 16 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 193 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 193 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 234 (accept_3_5 14 193 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 193 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 193 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 234
  (Polychromatic418967fa.accept_21_12_4_3_1_4924 12 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 234 (accept_3_5 11 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 234 (Polychromatic418967fa.accept_25_10_18_9_1_14027 10 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 234 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 234 (accept_3_5 8 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 193 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 234 (accept_3_5 5 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 234 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4 193 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 234 (accept_3_5 2 193 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 234))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 192 234 (Eq.refl Bool.true) (allA_succ_of_gcd 42 192 234 6 7 32 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 192 234
  (Polychromatic418967fa.accept_11_8_5_3_1_694 41 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 192 234 2 20 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 192 234 3 13 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 192 234 2 19 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 234 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 192 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 234 6 6 32 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 234
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 192 234 2 17 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 192 234 3 11 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 192 234 2 16 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 234 (Polychromatic418967fa.accept_19_12_2_6_1_9981 31 192
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 234 6 5 32 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 234
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 29 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 192 234 2 14 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 192 234 3 9 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 192 234 2 13 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 234 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 192
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 234 6 4 32 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 234
  (Polychromatic418967fa.accept_19_4_2_6_1_7181 23 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 192 234 2 11 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 192 234 3 7 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 192 234 2 10 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 192 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 192 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 234 6 3 32 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 234 2 8 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 192 234 3 5 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 192 234 2 7 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 192 234 (Polychromatic418967fa.accept_19_13_2_6_1_13962 13 192 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 234 6 2 32 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 234
  (Polychromatic418967fa.accept_27_11_3_18_1_14082 11 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 192 234 2 5 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 192 234 3 3 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 192 234 2 4 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 192 234 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 192 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 234 6 1 32 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 234
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 192 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 192 234 2 2 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 192 234 3 1 64 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 192 234 2 1 96 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 192 234 (Polychromatic418967fa.accept_19_1_2_6_1_4411 1 192 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 234))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 191 234
  (Eq.refl Bool.true) (allA_succ_of_accept 43 191 234 (accept_3_4 43 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 191 234 (Polychromatic418967fa.accept_17_8_4_13_1_3014 42 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 234 (accept_3_4 40 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 234
  (Polychromatic418967fa.accept_21_18_2_3_1_9685 39 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 191 234 (Polychromatic418967fa.accept_21_17_2_3_1_4942 38 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 234 (accept_3_4 37 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 191 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 191 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  35 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 234 (accept_3_4 34
  191 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 191 234 (Polychromatic418967fa.accept_15_2_11_9_1_263 32 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 234 (accept_3_4 31 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 191 234 (Polychromatic418967fa.accept_16_14_15_10_1_5910 30 191 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 234 (accept_3_4 28 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 191 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 234 (accept_3_4 25 191 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 234 (Polychromatic418967fa.accept_19_5_1_6_1_4361 24 191 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 234
  (Polychromatic418967fa.accept_20_3_11_14_1_5319 23 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 191 234 (accept_3_4 22 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 191 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 234 (accept_3_4 19 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 234 (Polychromatic418967fa.accept_11_7_4_3_1_302
  18 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 234 (accept_3_4 16 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 234 (Polychromatic418967fa.accept_16_14_15_10_1_5910 14 191 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 234 (accept_3_4 13 191 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 234
  (Polychromatic418967fa.accept_16_11_15_10_1_3515 11 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 191 234 (accept_3_4 10 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 191 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 234 (accept_3_4 7 191 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 234 (accept_3_4 4 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 234 (Polychromatic418967fa.accept_17_3_4_13_1_2030 3 191 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 234 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 191 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 234 (accept_3_4 1 191 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 234)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 190 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 190 234 2 22 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 190 234 (Polychromatic418967fa.accept_25_18_15_9_1_14081 43 190 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 190 234 2 21 95 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 190 234 (accept_3_5 41
  190 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 190 234 2 20 95 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 190 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 190 234 2 19 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 190 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 190 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 190 234 2 18 95 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 190 234 (accept_3_5 35 190 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 190 234 2 17 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 190 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 234 2 16 95 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 234
  (Polychromatic418967fa.accept_15_1_10_9_1_1495 31 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 234 2 15 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 234 (accept_3_5 29 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 234 2 14 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 190 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 234 2 13 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 234 2 12 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 234 (accept_3_5 23 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 234 2 11 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 234 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 190 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 234 2 10 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 234 2 9 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 234 (accept_3_5 17 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 234 2 8 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 190 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 234 2 7 95 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 234
  (Polychromatic418967fa.accept_16_13_14_10_1_1669 13 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 190 234 2 6 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 190 234 (accept_3_5 11 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 234 2 5 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 190 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 234 2 4 95 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 234
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 234 2 3 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 234 (accept_3_5 5 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  234 2 2 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 190 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 234 2 1 95 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 234 (Polychromatic418967fa.accept_15_1_10_9_1_1495 1 190 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 234)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 189 234 (Eq.refl Bool.true) (allA_succ_of_gcd 45 189 234 9 5 21 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 189 234
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 189 234 3 14 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 189 234 (Polychromatic418967fa.accept_17_7_2_13_1_5397
  41 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 234
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 189 234 3 13 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 189 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 189 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 234
  (Polychromatic418967fa.accept_16_5_13_10_1_3664 37 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 189 234 9 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 189 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 189 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 234
  (Polychromatic418967fa.accept_11_1_2_3_1_688 34 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 189 234 3 11 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 189 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 189 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 189 234 3 10 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 189 234
  (Polychromatic418967fa.accept_23_6_5_4_1_14080 29 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 189 234 9 3 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 189 234 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 234
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 189 234 3 8 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 189 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 234 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 189
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 234 3 7 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 234
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 234 9 2 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 234 (Polychromatic418967fa.accept_14_3_7_10_1_2146
  17 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 234
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 189 234 3 5 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 189 234 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 234 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 189
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 234 3 4 63 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 234 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 234 9 1 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 189 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 189 234 3 2 63 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 189 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 189 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 234 3 1 63 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 234
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 189 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 234 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 189 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 234)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 188 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 188 234 2 23 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 45 188 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 188 234 2 22 94 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 188 234 (accept_3_4 43
  188 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 188 234 2 21 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 188 234
  (Polychromatic418967fa.accept_19_3_17_6_1_1991 41 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 188 234 2 20 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 188 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 188 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 188 234 2 19 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 188 234 (accept_3_4 37 188 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 188 234 2 18 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 188 234 (Polychromatic418967fa.accept_11_2_1_3_1_683
  35 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 234 2 17 94 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 188 234 2 16 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 188 234 (accept_3_4 31 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 234 2 15 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 188 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 234 2 14 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 234 2 13 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 234 (accept_3_4 25 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 234 2 12 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 188 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 234 2 11 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 234 2 10 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 188 234 (accept_3_4 19 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 234 2 9 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 234 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 188 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 234 2 8 94 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 234 2 7 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 234 (accept_3_4 13 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 234 2 6 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 188 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 234 2 5 94 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 234 2 4 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 234 (accept_3_4 7 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  234 2 3 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 234 (Polychromatic418967fa.accept_16_5_12_10_1_3508 5 188 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 234 2 2 94 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 188 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 234 2 1 94 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 234 (accept_3_4 1 188 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 234))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 187 234 (Eq.refl Bool.true) (allA_succ_of_accept 47 187 234 (accept_3_5 47 187 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 187 234 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 187 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 234 (accept_3_5 44
  187 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 187 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 187 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 234 (accept_3_5 41 187 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 187 234 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 234
  (Polychromatic418967fa.accept_21_18_19_3_1_9649 39 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 187 234 (accept_3_5 38 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 187 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 187 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 234 (accept_3_5 35 187 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 234
  (Polychromatic418967fa.accept_19_15_16_6_1_9955 34 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 187 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 234 (accept_3_5 32 187 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 234 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 234 (accept_3_5 29 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 234 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 234 (Polychromatic418967fa.accept_19_8_16_6_1_5804 27 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 234 (accept_3_5 26 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 187 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 234
  (Polychromatic418967fa.accept_22_2_11_14_1_7783 24 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 187 234 (accept_3_5 23 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 187 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 187 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 187 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 234 (accept_3_5 20 187 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 234
  (Polychromatic418967fa.accept_22_19_11_14_1_14079 19 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 234 (Polychromatic418967fa.accept_21_18_19_3_1_9649 18 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 234 (accept_3_5 17 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 187 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 234 (accept_3_5 14 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 234 (accept_3_5 11 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 234 (Polychromatic418967fa.accept_19_10_16_6_1_5773 10 187
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 234 (accept_3_5 8 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 234 (Polychromatic418967fa.accept_19_7_16_6_1_4400 7 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 234 (Polychromatic418967fa.accept_21_6_19_3_1_4823 6 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 234 (accept_3_5 5 187 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 234 (Polychromatic418967fa.accept_27_4_25_18_1_14078 4 187
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 234
  (Polychromatic418967fa.accept_10_3_7_4_1_584 3 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 234 (accept_3_5 2 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 234)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 186 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 186 234 6 8 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 234 (Polychromatic418967fa.accept_19_9_15_6_1_4396 47 186 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 234 2 23 93 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 186 234 3 15 62 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 186 234 2 22 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 234 6 7 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 186 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 186 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 234 2 20 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 186 234 3 13 62 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 186 234 2 19 93 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 234
  (Polychromatic418967fa.accept_17_3_16_13_1_6635 37 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 186 234 6 6 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 186 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 186 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 234 2 17 93 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 186 234 3 11 62 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 186 234 2 16 93 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 234
  (Polychromatic418967fa.accept_15_1_6_9_1_254 31 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 234 6 5 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 186 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 186 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 234 2 14 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 186 234 3 9 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 186 234 2 13 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 234 6 4 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 186 234 (Polychromatic418967fa.accept_19_4_15_6_1_9954 23 186 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 234 2 11 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 186 234 3 7 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 186 234 2 10 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 234
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 234 6 3 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 234 (Polychromatic418967fa.accept_21_17_18_3_1_4909 17 186 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 234 2 8 93 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 234 3 5 62 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 234 2 7 93 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 234 6 2 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 234 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 186 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 234 2 5 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 234 3 3 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 234 2 4 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 7
  186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 234 6 1 31 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 186 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 186 234 2 2 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 186 234 3 1 62 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 186 234 2 1 93 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 186 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 186 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 234))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 185
  234 (Eq.refl Bool.true) (allA_succ_of_accept 49 185 234 (accept_3_4 49 185 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 185 234 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 234 (accept_3_4 46 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 185 234 (Polychromatic418967fa.accept_17_11_15_13_1_11717 45 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 234 (Polychromatic418967fa.accept_15_14_5_9_1_2284 44 185 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 234 (accept_3_4 43 185 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 234
  (Polychromatic418967fa.accept_15_12_5_9_1_3234 42 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 185 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 41 185 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 234 (accept_3_4 40 185 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 185 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 185 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 234
  (Polychromatic418967fa.accept_25_13_10_9_1_8706 38 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 185 234 (accept_3_4 37 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 185 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 185 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 185 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 234 (accept_3_4 34 185 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 234 (Polychromatic418967fa.accept_15_3_5_9_1_764
  33 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 234
  (Polychromatic418967fa.accept_25_7_10_9_1_14077 32 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 185 234 (accept_3_4 31 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 185 234 (Polychromatic418967fa.accept_19_11_14_6_1_4378 30 185 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 234 (Polychromatic418967fa.accept_10_9_5_4_1_966
  29 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 234 (accept_3_4 28
  185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 185 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 185 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 234 (accept_3_4 25 185 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 185 234 (Polychromatic418967fa.accept_19_5_14_6_1_4413 24 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 234 (accept_3_4 22 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 234 (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 234 (accept_3_4 19 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 185
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 234
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 234 (accept_3_4 16 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 234 (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 234 (accept_3_4 13 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 234 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 185
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 234 (accept_3_4 10 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 234 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 234 (Polychromatic418967fa.accept_17_8_15_13_1_7942 8 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 234 (accept_3_4 7 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 185 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 234
  (Polychromatic418967fa.accept_17_5_15_13_1_7936 5 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 234 (accept_3_4 4 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 234 (Polychromatic418967fa.accept_17_2_15_13_1_3034 2 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 234 (accept_3_4 1 185 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 185 234)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 184
  234 (Eq.refl Bool.true) (allA_succ_of_gcd 50 184 234 2 25 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 184 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 184 234 2 24 92 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 184 234 (accept_3_5 47
  184 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 184 234 2 23 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 184 234
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 184 234 2 22 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 184 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 184 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 184 234 2 21 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 184 234 (accept_3_5 41 184 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 184 234 2 20 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 184 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236
  39 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 234 2 19 92 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 234
  (Polychromatic418967fa.accept_27_10_22_18_1_14076 37 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 184 234 2 18 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 184 234 (accept_3_5 35 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 184 234 2 17 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 184 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 184 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 234 2 16 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 234
  (Polychromatic418967fa.accept_19_12_13_6_1_7130 31 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 184 234 2 15 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 184 234 (accept_3_5 29 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 234 2 14 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 184 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 184 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 234 2 13 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 234
  (Polychromatic418967fa.accept_15_10_4_9_1_3203 25 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 234 2 12 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 184 234 (accept_3_5 23 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 184 234 2 11 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 184 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 184 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 234 2 10 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 234 2 9 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 234 (accept_3_5 17 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 234 2 8 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 184 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 184 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 234 2 7 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 234 2 6 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 184 234 (accept_3_5 11 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 234 2 5 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 184 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 234 2 4 92 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 234
  (Polychromatic418967fa.accept_19_7_13_6_1_1914 7 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 234 2 3 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 234 (accept_3_5 5 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  234 2 2 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 184 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 234 2 1 92 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184
  234))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 183 234 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  183 234 3 17 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 183 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 183 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 183 234 3 16 61 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 183 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 183 234 3 15 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 183 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 234
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 183 234 3 14 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 183 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 234 (Polychromatic418967fa.accept_7_5_1_3_1_103
  40 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 183 234 3 13 61 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 183 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 183 234 3 12 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 183 234 (Polychromatic418967fa.accept_15_5_3_9_1_283
  35 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 183 234 3 11 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 183 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 183 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 234
  (Polychromatic418967fa.accept_20_11_3_14_1_5336 31 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 183 234 3 10 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 183 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 234
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 234 3 9 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 183 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 234 3 8 61 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 234 3 7 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 234 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 183 234 3 6 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 183 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 234 3 5 61 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 234 3 4 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 234
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 234 3 3 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 234 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 183 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 234 3 2 61 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 183 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 234 3 1 61 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 183 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 234)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 182 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 52 182 234 26 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 182 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 182 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 182 234 2 25 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 182 234 (accept_3_4 49 182 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 182 234 2 24 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 182 234 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 182 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 234 2 23 91 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 234 2 22 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 234 (accept_3_4 43 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 234 2 21 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 182 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 234 2 20 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 182 234 13 3 14 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 182 234 2 19 91 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 182 234 (accept_3_4 37
  182 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 182 234 2 18 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 182 234
  (Polychromatic418967fa.accept_17_1_12_13_1_448 35 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 182 234 2 17 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 182 234 (Polychromatic418967fa.accept_12_9_2_6_1_455 33 182 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 234 2 16 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 234 (accept_3_4 31 182 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 234 2 15 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 234 (Polychromatic418967fa.accept_21_8_14_3_1_9602
  29 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 234 2 14 91 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 234 26 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 182 234 (accept_3_4 25 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24
  182 234 2 12 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 182 234 (Polychromatic418967fa.accept_15_8_2_9_1_3200 23 182 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 234 2 11 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 234 (Polychromatic418967fa.accept_12_9_2_6_1_455
  21 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 182 234 2 10 91 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 234
  (accept_3_4 19 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 182 234 2 9 91 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 182 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 182 234 2 8 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 182 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 182 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 182 234 2 7 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 182 234 13 1 14 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 182 234 2 6 91 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 182 234
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 182 234 2 5 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 182 234 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 182 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 182 234 2 4 91 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 182 234 (accept_3_4 7 182 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182 234 2 3 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 182 234 (Polychromatic418967fa.accept_19_5_11_6_1_1909
  5 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 234 2 2 91 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 234
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 182 234 2 1 91 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 182 234 (accept_3_4 1 182 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  234))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 181 234 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 181 234 (accept_3_5 53 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 181 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 52 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 181 234 (accept_3_5 50 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 181 234 (Polychromatic418967fa.accept_17_15_11_13_1_2039 49 181 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 181 234
  (Polychromatic418967fa.accept_21_6_13_3_1_4851 48 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 181 234 (accept_3_5 47 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 181 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 181 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 181 234 (accept_3_5 44 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 181 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 181 234
  (Polychromatic418967fa.accept_19_4_10_6_1_11380 42 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 181 234 (accept_3_5 41 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 181 234 (Polychromatic418967fa.accept_15_10_1_9_1_5356 40 181 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 181 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 234 (accept_3_5 38 181 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 234 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 181 234
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 181 234 (accept_3_5 35 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 181 234 (Polychromatic418967fa.accept_19_15_10_6_1_7169 34 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 181 234 (Polychromatic418967fa.accept_19_14_10_6_1_4372 33 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 234 (accept_3_5 32 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 181 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 181 234 (accept_3_5 29 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 181 234 (Polychromatic418967fa.accept_16_12_5_10_1_3561 28 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 234 (accept_3_5 26 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 234
  (Polychromatic418967fa.accept_17_7_11_13_1_2037 24 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 181 234 (accept_3_5 23 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 181 234 (Polychromatic418967fa.accept_15_7_1_9_1_1500 22 181 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 234 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 181
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 234 (accept_3_5 20 181
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 181 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 181 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 234 (accept_3_5 17 181 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 181 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 234 (accept_3_5 14
  181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 234
  (Polychromatic418967fa.accept_16_13_5_10_1_1680 13 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 234 (Polychromatic418967fa.accept_16_12_5_10_1_3561 12 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 234 (accept_3_5 11 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 234 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 181
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 234 (accept_3_5 8 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 234 (Polychromatic418967fa.accept_15_6_1_9_1_1476 6 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 234 (accept_3_5 5 181 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 234 (accept_3_5 2 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 234 (Polychromatic418967fa.accept_19_1_10_6_1_5726 1 181 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 234)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 180 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 180 234 18 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 180 234 (Polychromatic418967fa.accept_19_15_9_6_1_8667 53 180 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 234 2 26 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 180 234 3 17 60 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 180 234 2 25 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 180 234
  (Polychromatic418967fa.accept_21_7_12_3_1_4849 49 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 234 6 8 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 180 234 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 180 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 234 2 23 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 234 9 5 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 234 2 22 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 234 6 7 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 180 234 (Polychromatic418967fa.accept_19_3_9_6_1_12696 41 180 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 234 2 20 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 234 3 13 60 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 180 234 2 19 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 234 18 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 234 (Polychromatic418967fa.accept_19_16_9_6_1_5799 35 180 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 234 2 17 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 234 3 11 60 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 234 2 16 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 234
  (Polychromatic418967fa.accept_17_14_10_13_1_4147 31 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 180 234 6 5 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 180 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 180 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 234 2 14 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 234 9 3 20 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 234 2 13 90 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 234
  (Polychromatic418967fa.accept_21_4_12_3_1_12610 25 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 180 234 6 4 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 180 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 234 2 11 90 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 234 3 7 60 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 234 2 10 90 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 234
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 234 18 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 234 (Polychromatic418967fa.accept_19_17_9_6_1_12658 17 180 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 234 2 8 90 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 234 3 5 60 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 234 2 7 90 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 234
  (Polychromatic418967fa.accept_19_13_9_6_1_4393 13 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 234 6 2 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 180 234 (Polychromatic418967fa.accept_21_11_12_3_1_6461 11 180 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 234 2 5 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 234 9 1 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 234 2 4 90 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 234
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 234 6 1 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 234 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 180 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 234 2 2 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 234 3 1 60 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 234 2 1 90 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  180 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 179 234 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 179 234 (accept_3_4 55 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 179 234 (Polychromatic418967fa.accept_19_16_8_6_1_4407 54 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 234 (accept_3_4 52 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 234 (Polychromatic418967fa.accept_15_6_14_9_1_1471 51 179 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 234 (accept_3_4 49 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 234 (Polychromatic418967fa.accept_25_22_4_9_1_10585 47 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 234 (accept_3_4 46 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 179 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 234
  (Polychromatic418967fa.accept_16_12_3_10_1_3524 44 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 179 234 (accept_3_4 43 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 179 234 (Polychromatic418967fa.accept_15_12_14_9_1_778 42 179 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 179 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 234 (accept_3_4 40 179 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 234
  (Polychromatic418967fa.accept_16_7_3_10_1_3614 39 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 179 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 179 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 234 (accept_3_4 37 179 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 179 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420
  35 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 234 (accept_3_4 34
  179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 179 234 (Polychromatic418967fa.accept_19_13_8_6_1_7195 32 179 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 234 (accept_3_4 31 179 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 179 234 (Polychromatic418967fa.accept_24_6_11_18_1_14075 30 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 234 (accept_3_4 28 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 234 (Polychromatic418967fa.accept_19_7_8_6_1_3123 26 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 234 (accept_3_4 25 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 234 (Polychromatic418967fa.accept_20_4_19_14_1_5327 24 179
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 234
  (Polychromatic418967fa.accept_10_3_9_4_1_960 23 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 234 (accept_3_4 22 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 234 (accept_3_4 19 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 234 (accept_3_4 16 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 234 (Polychromatic418967fa.accept_19_14_8_6_1_981 14 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 234 (accept_3_4 13 179 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 234 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 179
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 234
  (Polychromatic418967fa.accept_22_11_3_14_1_9378 11 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 179 234 (accept_3_4 10 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 179 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 179 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 234 (accept_3_4 7 179 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 234 (accept_3_4 4 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 234 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 179 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 234 (Polychromatic418967fa.accept_19_2_8_6_1_1905 2 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 234 (accept_3_4 1 179 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 178 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 178 234 2 28 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 178 234 (Polychromatic418967fa.accept_17_4_8_13_1_7960 55 178
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 178 234 2 27 89 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 178 234 (accept_3_5 53
  178 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 178 234 2 26 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 178 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 51 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 178 234 2 25 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 178 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 49 178 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 178 234 2 24 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 178 234 (accept_3_5 47 178 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 178 234 2 23 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 178 234 (Polychromatic418967fa.accept_11_1_2_3_1_688
  45 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 234 2 22 89 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 234
  (Polychromatic418967fa.accept_19_5_7_6_1_11379 43 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 234 2 21 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 234 (accept_3_5 41 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 234 2 20 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 178 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 234 2 19 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 234
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 37 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 234 2 18 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 234 (accept_3_5 35 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 234 2 17 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 234 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 178 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 234 2 16 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 234
  (Polychromatic418967fa.accept_24_7_10_18_1_10688 31 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 178 234 2 15 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 178 234 (accept_3_5 29 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 234 2 14 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 178 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 234 2 13 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 234
  (Polychromatic418967fa.accept_22_3_2_14_1_14074 25 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 178 234 2 12 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 178 234 (accept_3_5 23 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 234 2 11 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 234 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 178 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 234 2 10 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 234 2 9 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 234 (accept_3_5 17 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 234 2 8 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 178 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 234 2 7 89 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 234
  (Polychromatic418967fa.accept_19_13_7_6_1_5826 13 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 234 2 6 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 234 (accept_3_5 11 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 234 2 5 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 178 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 234 2 4 89 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 234
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 234 2 3 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 234 (accept_3_5 5 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  234 2 2 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 178 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 234 2 1 89 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 234 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 178 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 177 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 177 234 3 19 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 177 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 177 234 3 18 59 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 177 234
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 177 234 3 17 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 177 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 50
  177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 234
  (Polychromatic418967fa.accept_15_4_12_9_1_773 49 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 177 234 3 16 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 177 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 234 (Polychromatic418967fa.accept_11_2_1_3_1_683
  46 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 177 234 3 15 59 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 177 234
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 177 234 3 14 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 177 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 177 234 3 13 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 177 234 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 177 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 234
  (Polychromatic418967fa.accept_21_16_9_3_1_6436 37 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 177 234 3 12 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 177 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 234 (Polychromatic418967fa.accept_7_6_2_3_1_107
  34 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 177 234 3 11 59 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 234
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 177 234 3 10 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 177 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 234
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 177 234 3 9 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 177 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 234 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 177
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 234 3 8 59 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 234 3 7 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 177 234 3 6 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 177 234 (Polychromatic418967fa.accept_21_17_9_3_1_6437 17 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 177
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 234 3 5 59 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 234
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 234 3 4 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 234
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 234 3 3 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 234 3 2 59 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 177 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 234 3 1 59 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 177 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 176 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 176 234 2 29 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 176 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 176 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 176 234 2 28 88 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 176 234 (accept_3_4 55 176 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 176 234 2 27 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 234 2 26 88 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 234 2 25 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 234 (accept_3_4 49 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 234 2 24 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 176 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 234 2 23 88 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 234 2 22 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 234 (accept_3_4 43 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 234 2 21 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 234 (Polychromatic418967fa.accept_17_7_6_13_1_10548 41 176 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 234 2 20 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 234 2 19 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 234 (accept_3_4 37 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 234 2 18 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 176 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 176 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 234 2 17 88 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 234 2 16 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 234 (accept_3_4 31 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 234 2 15 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 234 (Polychromatic418967fa.accept_37_29_28_12_1_14073 29 176 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 234 2 14 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 234 2 13 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 234 (accept_3_4 25 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 234 2 12 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 176 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 234 2 11 88 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 234 2 10 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 234 (accept_3_4 19 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 234 2 9 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 234 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 176 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 234 2 8 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 234 2 7 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 234 (accept_3_4 13 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 234 2 6 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 176 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 234 2 5 88 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 234 2 4 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 234 (accept_3_4 7 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  234 2 3 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 176 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 234 2 2 88 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 176 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 234 2 1 88 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 234 (accept_3_4 1 176 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 175 234 (Eq.refl Bool.true) (allA_succ_of_accept 59 175 234 (accept_3_5 59 175 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 175 234 (Polychromatic418967fa.accept_21_16_7_3_1_8093 58 175 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 175 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 175 234 (accept_3_5 56 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 175 234 (Polychromatic418967fa.accept_19_17_4_6_1_5810 55 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 175 234 (Polychromatic418967fa.accept_21_12_7_3_1_4927 54 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 175 234 (accept_3_5 53 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 175 234 (Polychromatic418967fa.accept_21_10_7_3_1_4884 52 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 234
  (Polychromatic418967fa.accept_10_1_5_4_1_276 51 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 175 234 (accept_3_5 50 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 175 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 175 234 (Polychromatic418967fa.accept_15_3_10_9_1_769 48 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 234 (accept_3_5 47 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 175 234 (accept_3_5 44 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 175 234 (Polychromatic418967fa.accept_16_11_15_10_1_3515 43 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 234 (Polychromatic418967fa.accept_15_12_10_9_1_798 42 175 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 234 (accept_3_5 41 175 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 234 (Polychromatic418967fa.accept_11_7_10_3_1_633
  40 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 234
  (Polychromatic418967fa.accept_10_9_5_4_1_966 39 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 234 (accept_3_5 38 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 234 (accept_3_5 35 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 234 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 234 (accept_3_5 32 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 234 (Polychromatic418967fa.accept_16_14_15_10_1_5910 30 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 234 (accept_3_5 29 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 234 (Polychromatic418967fa.accept_20_8_15_14_1_1487 28 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 234
  (Polychromatic418967fa.accept_15_12_10_9_1_798 27 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 234 (accept_3_5 26 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 234 (Polychromatic418967fa.accept_19_5_4_6_1_11375 24 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 234 (accept_3_5 23 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 234 (Polychromatic418967fa.accept_19_3_4_6_1_9976 22 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 234 (accept_3_5 20 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 234 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 234 (accept_3_5 17 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 234
  (Polychromatic418967fa.accept_17_15_5_13_1_6626 15 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 175 234 (accept_3_5 14 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 175 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 234 (Polychromatic418967fa.accept_15_12_10_9_1_798 12 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 234 (accept_3_5 11 175
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 234
  (Polychromatic418967fa.accept_17_10_5_13_1_12853 10 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 234 (accept_3_5 8 175 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 234
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 234 (accept_3_5 5 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 234 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 175 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 234 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 234 (accept_3_5 2 175 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 174 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 174 234 6 10 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 234 (Polychromatic418967fa.accept_14_3_6_10_1_752 59 174 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 234 2 29 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 174 234 3 19 58 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 174 234 2 28 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 174 234
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 55 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 174 234 6 9 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 174 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 174 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 234 2 26 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 174 234 3 17 58 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 234 2 25 87 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 234
  (Polychromatic418967fa.accept_21_7_6_3_1_8072 49 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 234 6 8 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 174 234 (Polychromatic418967fa.accept_16_15_14_10_1_9549 47 174 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 234 2 23 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 174 234 3 15 58 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 234 2 22 87 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 234
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 43 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 234 6 7 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 234 (Polychromatic418967fa.accept_21_20_6_3_1_9691 41 174 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 234 2 20 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 234 3 13 58 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 234 2 19 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 234 6 6 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 174 234 (Polychromatic418967fa.accept_19_16_3_6_1_1941 35 174 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 234 2 17 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 234 3 11 58 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 234 2 16 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 234
  (Polychromatic418967fa.accept_14_3_6_10_1_752 31 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 234 6 5 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 174 234 (Polychromatic418967fa.accept_16_13_14_10_1_1669 29 174 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 234 2 14 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 234 3 9 58 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 234 2 13 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 234 6 4 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 174 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 234 2 11 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 234 3 7 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 234 2 10 87 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 234
  (Polychromatic418967fa.accept_21_19_6_3_1_13999 19 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 174 234 6 3 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 174 234 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 174 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 234 2 8 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 234 3 5 58 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 234 2 7 87 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 234
  (Polychromatic418967fa.accept_16_13_14_10_1_1669 13 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 174 234 6 2 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 174 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 174 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 234 2 5 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 234 3 3 58 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 234 2 4 87 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 234
  (Polychromatic418967fa.accept_16_7_14_10_1_3544 7 174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 234 6 1 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 234 (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 174 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 234 2 2 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 234 3 1 58 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 234 2 1 87 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 234 (Polychromatic418967fa.accept_19_1_3_6_1_5827 1
  174 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 173 234 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 173 234 (accept_3_4 61 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 234 (accept_3_4 58 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 234
  (Polychromatic418967fa.accept_27_2_11_18_1_6265 56 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 173 234 (accept_3_4 55 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 173 234 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 234
  (Polychromatic418967fa.accept_16_5_13_10_1_3664 53 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 173 234 (accept_3_4 52 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 173 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 173 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 173 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 234 (accept_3_4 49 173 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 234 (Polychromatic418967fa.accept_15_3_8_9_1_795
  48 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 234 (accept_3_4 46 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 234 (Polychromatic418967fa.accept_25_20_23_9_1_12231 45 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 234 (accept_3_4 43 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 234 (Polychromatic418967fa.accept_17_8_3_13_1_5372 42 173
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 234
  (Polychromatic418967fa.accept_19_3_2_6_1_11398 41 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 234 (accept_3_4 40 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 38 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 234 (accept_3_4 37 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 234 (accept_3_4 34 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 234 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 234 (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 234 (accept_3_4 31 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 173 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 234 (accept_3_4 28 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 234 (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 234 (accept_3_4 25 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 234 (Polychromatic418967fa.accept_20_4_13_14_1_13984 24
  173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 234 (accept_3_4 22 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 234 (Polychromatic418967fa.accept_16_5_13_10_1_3664 21 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 234 (Polychromatic418967fa.accept_19_1_2_6_1_4411 20 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 234 (accept_3_4 19 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 234 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 173
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 234
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 234 (accept_3_4 16 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 234 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 234 (accept_3_4 13 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 234 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 173
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 234 (accept_3_4 10 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 234 (accept_3_4 7 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 173 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 234
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 234 (accept_3_4 4 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 234 (accept_3_4 1 173 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  172 234 (Eq.refl Bool.true) (allA_succ_of_gcd 62 172 234 2 31 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 172 234 (Polychromatic418967fa.accept_15_1_7_9_1_20 61 172 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 172 234 2 30 86 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 172 234 (accept_3_5 59
  172 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 172 234 2 29 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 172 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 172 234 2 28 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 172 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 172 234 2 27 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 172 234 (accept_3_5 53 172 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 172 234 2 26 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 172 234 (Polychromatic418967fa.accept_12_3_4_6_1_434
  51 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 172 234 2 25 86 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 172 234
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 49 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 172 234 2 24 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 172 234 (accept_3_5 47 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 172 234 2 23 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 172 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 234 2 22 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 234 2 21 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 234 (accept_3_5 41 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 234 2 20 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 234 2 19 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 234 2 18 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 172 234 (accept_3_5 35 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 172 234 2 17 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 172 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 234 2 16 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 234
  (Polychromatic418967fa.accept_15_1_7_9_1_20 31 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 172 234 2 15 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 172 234 (accept_3_5 29 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 172 234 2 14 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 172 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 234 2 13 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 234
  (Polychromatic418967fa.accept_23_2_11_4_1_14053 25 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 172 234 2 12 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 172 234 (accept_3_5 23 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 234 2 11 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 234 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 172 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 234 2 10 86 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 234
  (Polychromatic418967fa.accept_16_3_12_10_1_315 19 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 234 2 9 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 234 (accept_3_5 17 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 234 2 8 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 172 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 234 2 7 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 234 2 6 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 172 234 (accept_3_5 11 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 234 2 5 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 172 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 234 2 4 86 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 234 2 3 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 234 (accept_3_5 5 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  234 2 2 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 172 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 234 2 1 86 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 171 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 171 234 9 7 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 171 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 171 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 171 234 3 20 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 171 234
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 171 234 3 19 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 171 234 (Polychromatic418967fa.accept_12_8_3_6_1_909
  56 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 234
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 171 234 9 6 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 171
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 171 234 3 17 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 171 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 171 234 3 16 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 171 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  47 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 171 234 9 5 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 171 234 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 234 (Polychromatic418967fa.accept_20_3_11_14_1_5319 43 171
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 171 234 3 14 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 171 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 234 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 171 234 3 13 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 234 (Polychromatic418967fa.accept_12_2_3_6_1_112
  38 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 171 234 9 4 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 171 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 171
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 234 3 11 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 234
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 234 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 234 3 10 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 234
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 171 234 9 3 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 171 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 234 3 8 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 234
  (Polychromatic418967fa.accept_20_3_11_14_1_5319 23 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 171 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 234 3 7 57 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 234
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 234 9 2 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 234
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 234 3 5 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 234 3 4 57 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 234
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 234 9 1 19 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 8 171 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 234
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 171 234 3 2 57 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 234 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 171 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 234 3 1 57 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 171 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 170 234 (Eq.refl Bool.true) (allA_succ_of_gcd 64 170 234 2 32 85 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 234
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 234 2 31 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 234 (accept_3_4 61 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 234 2 30 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 234 (Polychromatic418967fa.accept_15_14_5_9_1_2284 59 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 234 2 29 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 234 2 28 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 234 (accept_3_4 55 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 234 2 27 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 234 (Polychromatic418967fa.accept_27_26_8_18_1_6258 53 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 234 2 26 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 234
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 234 2 25 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 234 (accept_3_4 49 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 234 2 24 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 170 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 234 2 23 85 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 234 2 22 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 234 (accept_3_4 43 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 234 2 21 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 170 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 234 2 20 85 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 234
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 234 2 19 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 234 (accept_3_4 37 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 234 2 18 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 234 (Polychromatic418967fa.accept_20_15_10_14_1_11245 35 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 234 2 17 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 234 2 16 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 234 (accept_3_4 31 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 234 2 15 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 170 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 234 2 14 85 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 234 2 13 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 234 (accept_3_4 25 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 234 2 12 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 234 (Polychromatic418967fa.accept_24_23_2_18_1_5318 23 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 234 2 11 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 234 2 10 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 234 (accept_3_4 19 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 234 2 9 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 234 (Polychromatic418967fa.accept_19_17_18_6_1_7192 17 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 234 2 8 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 234 2 7 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 234 (accept_3_4 13 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 234 2 6 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 234 (Polychromatic418967fa.accept_15_11_5_9_1_3205 11 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 234 2 5 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 234 2 4 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 234 (accept_3_4 7 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  234 2 3 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 170 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 234 2 2 85 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 170 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 234 2 1 85 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 234 (accept_3_4 1 170 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 169 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 169 234 13 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 169 234 (Polychromatic418967fa.accept_20_4_9_14_1_5316 64 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 169 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 169 234 (accept_3_5 62 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 169 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 169 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 169 234 (accept_3_5 59 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 234
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 57 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 234 (accept_3_5 56 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 234 (accept_3_5 53 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 169 234 13 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 169 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 169 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 234 (accept_3_5 50 169 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 169 234
  (Polychromatic418967fa.accept_16_1_9_10_1_4740 49 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 169 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 234 (accept_3_5 47 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 169 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420
  45 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 234 (accept_3_5 44
  169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 169 234 (Polychromatic418967fa.accept_15_12_4_9_1_3204 42 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 234 (accept_3_5 41 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 169 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 169 234 13 3 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 169 234 (accept_3_5 38 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 234
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 234 (accept_3_5 35 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 234 (Polychromatic418967fa.accept_22_12_15_14_1_9353 34 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 234 (accept_3_5 32 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 169 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 234 (accept_3_5 29 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 169 234 13 2 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 169 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 169 234 (Polychromatic418967fa.accept_20_4_9_14_1_5316 24 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 234 (accept_3_5 23 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 169 234 (Polychromatic418967fa.accept_19_3_17_6_1_1991 22 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 234
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 234 (accept_3_5 20 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 234 (accept_3_5 17 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 234 (accept_3_5 14 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13
  169 234 13 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 169 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 234 (accept_3_5 11 169 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 169 234 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 234 (accept_3_5 8 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 234 (Polychromatic418967fa.accept_15_6_4_9_1_1438 6 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 234 (accept_3_5 5 169 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 234 (accept_3_5 2 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 234 (Polychromatic418967fa.accept_16_1_9_10_1_4740 1 169 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 168 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 168 234 6 11 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 168 234 (Polychromatic418967fa.accept_15_5_3_9_1_283 65 168 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 234 2 32 84 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 168 234 3 21 56 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 168 234 2 31 84
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 168 234
  (Polychromatic418967fa.accept_27_7_6_18_1_14072 61 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 168 234 6 10 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 168 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 168 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 234 2 29 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 168 234 3 19 56 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 234 2 28 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 234
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 55 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 234 6 9 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 168 234 (Polychromatic418967fa.accept_15_8_3_9_1_4220 53 168 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 234 2 26 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 168 234 3 17 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 234 2 25 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 234 6 8 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 168 234 (Polychromatic418967fa.accept_19_9_16_6_1_5774 47 168 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 234 2 23 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 168 234 3 15 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 234 2 22 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 234
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 234 6 7 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 168 234 (Polychromatic418967fa.accept_19_3_16_6_1_1987 41 168 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 234 2 20 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 234 3 13 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 234 2 19 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 234
  (Polychromatic418967fa.accept_23_14_7_4_1_14071 37 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 168 234 6 6 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 168 234 (Polychromatic418967fa.accept_15_5_3_9_1_283 35 168 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 234 2 17 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 168 234 3 11 56 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 234 2 16 84 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 234
  (Polychromatic418967fa.accept_19_12_16_6_1_7175 31 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 168 234 6 5 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 168 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 168 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 234 2 14 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 234 3 9 56 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 234 2 13 84 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 234
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 234 6 4 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 234 (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 168 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 234 2 11 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 234 3 7 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 234 2 10 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 234 6 3 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 234 (Polychromatic418967fa.accept_29_17_23_2_1_14070 17 168 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 234 2 8 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 234 3 5 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 234 2 7 84 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 234
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 234 6 2 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 234 (Polychromatic418967fa.accept_17_11_15_13_1_11717 11 168 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 234 2 5 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 234 3 3 56 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 234 2 4 84 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 234
  (Polychromatic418967fa.accept_19_7_16_6_1_4400 7 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 234 6 1 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 234 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 168 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 234 2 2 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 234 3 1 56 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 234 2 1 84 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 234 (Polychromatic418967fa.accept_27_1_6_18_1_14069
  1 168 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 167 234 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 167 234 (accept_3_4 67 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 167 234 (Polychromatic418967fa.accept_19_9_15_6_1_4396 66 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 234 (accept_3_4 64 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 234 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 234
  (Polychromatic418967fa.accept_10_2_7_4_1_967 62 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 167 234 (accept_3_4 61 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 167 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 234 (Polychromatic418967fa.accept_14_3_13_10_1_761 59 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 234 (accept_3_4 58 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 167 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 234
  (Polychromatic418967fa.accept_11_1_2_3_1_688 56 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 234 (accept_3_4 55 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 234 (Polychromatic418967fa.accept_19_16_15_6_1_12661 54 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 234 (accept_3_4 52 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 167 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 234
  (Polychromatic418967fa.accept_19_12_15_6_1_7138 50 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 167 234 (accept_3_4 49 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 167 234 (Polychromatic418967fa.accept_19_10_15_6_1_5772 48 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 234
  (Polychromatic418967fa.accept_19_9_15_6_1_4396 47 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 234 (accept_3_4 46 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 234 (accept_3_4 43 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 234 (accept_3_4 40 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 234 (Polychromatic418967fa.accept_15_8_2_9_1_3200 38 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 234 (accept_3_4 37 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 234 (Polychromatic418967fa.accept_24_12_23_18_1_7127 36
  167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 234
  (Polychromatic418967fa.accept_16_3_7_10_1_3503 35 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 234 (accept_3_4 34 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 234 (accept_3_4 31 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 234 (accept_3_4 28 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 234 (Polychromatic418967fa.accept_17_10_14_13_1_12880 27 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 234 (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 167 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 234 (accept_3_4 25 167 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 234
  (Polychromatic418967fa.accept_19_5_15_6_1_1986 24 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 167 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 234 (accept_3_4 22 167 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 234
  (Polychromatic418967fa.accept_25_20_17_9_1_14068 20 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 167 234 (accept_3_4 19 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 167 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 167 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 234 (accept_3_4 16 167 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 234
  (Polychromatic418967fa.accept_22_15_13_14_1_14067 15 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 234 (Polychromatic418967fa.accept_16_14_7_10_1_898 14 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 234 (accept_3_4 13 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 167
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 234 (accept_3_4 10 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 234 (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 234 (accept_3_4 7 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 234 (Polychromatic418967fa.accept_21_6_20_3_1_9617 6 167 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 234 (accept_3_4 4 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 234 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 167 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 234 (accept_3_4 1 167 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 166 234 (Eq.refl Bool.true) (allA_succ_of_gcd 68 166 234 2 34 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 166 234 (Polychromatic418967fa.accept_15_7_1_9_1_1500
  67 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 166 234 2 33 83 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 166 234
  (accept_3_5 65 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 166 234 2 32 83 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 166 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 166 234 2 31 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 166 234 (Polychromatic418967fa.accept_14_5_12_10_1_2985 61 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 166 234 2 30 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 166 234 (accept_3_5 59 166 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 166 234 2 29 83 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 166 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 166 234 2 28 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 166 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 55 166 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 166 234 2 27 83 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 166 234 (accept_3_5 53 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 166 234 2 26 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 166 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 51
  166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 234 2 25 83 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 234
  (Polychromatic418967fa.accept_19_11_14_6_1_4378 49 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 166 234 2 24 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 166 234 (accept_3_5 47 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 234 2 23 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 166 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 234 2 22 83 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 234 2 21 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 234 (accept_3_5 41 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 234 2 20 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 234 2 19 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 234 2 18 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 234 (accept_3_5 35 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 234 2 17 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 234 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 234 2 16 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 234
  (Polychromatic418967fa.accept_19_12_14_6_1_12670 31 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 166 234 2 15 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 166 234 (accept_3_5 29 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 234 2 14 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 234 2 13 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 234
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 234 2 12 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 234 (accept_3_5 23 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 234 2 11 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 234 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 234 2 10 83 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 234
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 166 234 2 9 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 166 234 (accept_3_5 17 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 234 2 8 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 166 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 234 2 7 83 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 234
  (Polychromatic418967fa.accept_11_2_1_3_1_683 13 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 234 2 6 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 234 (accept_3_5 11 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 234 2 5 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 166 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 234 2 4 83 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 234
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 234 2 3 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 234 (accept_3_5 5 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  234 2 2 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 166 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 234 2 1 83 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 166 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 165 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 165 234 3 23 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 165 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 165 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 165 234 3 22 55 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 165 234
  (Polychromatic418967fa.accept_19_8_13_6_1_7153 65 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 165 234 3 21 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 165 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 62
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 234
  (Polychromatic418967fa.accept_10_1_5_4_1_276 61 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 234 3 20 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 165 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 234
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 165 234 3 19 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 165 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 165 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 165 234 3 18 55 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 165 234
  (Polychromatic418967fa.accept_19_15_13_6_1_8636 53 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 165 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 165 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 165 234 3 17 55 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 165 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 165 234 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 165 234 3 16 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 234
  (Polychromatic418967fa.accept_10_6_5_4_1_571 46 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 165 234 3 15 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 165 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 165 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 234 3 14 55 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 234 3 13 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 234 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 234
  (Polychromatic418967fa.accept_21_16_18_3_1_8050 37 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 165 234 3 12 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 165 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 165 234 3 11 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 165 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 165 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 234 3 10 55 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 234 3 9 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 234 (Polychromatic418967fa.accept_10_6_5_4_1_571
  26 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 234
  (Polychromatic418967fa.accept_21_4_18_3_1_11175 25 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 165 234 3 8 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 234 3 7 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 165 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 234 3 6 55 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 234
  (Polychromatic418967fa.accept_19_17_13_6_1_8670 17 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 165 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 165 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 234 3 5 55 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 234
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 234 3 4 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 234
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 165 234 3 3 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 234 3 2 55 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 234
  (Polychromatic418967fa.accept_21_5_18_3_1_4908 5 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 165 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 234 3 1 55 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 234 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 165 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 164 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 164 234 2 35 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 164 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 164 234 2 34 82 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 164 234 (accept_3_4 67
  164 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 164 234 2 33 82 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 164 234
  (Polychromatic418967fa.accept_15_5_14_9_1_274 65 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 164 234 2 32 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 164 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 164 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 164 234 2 31 82 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 164 234 (accept_3_4 61 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 164 234 2 30 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 164 234 (Polychromatic418967fa.accept_19_2_12_6_1_5816
  59 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 234 2 29 82 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 234 2 28 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 234 (accept_3_4 55 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 234 2 27 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 234 (Polychromatic418967fa.accept_15_8_14_9_1_4216 53 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 234 2 26 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 234
  (Polychromatic418967fa.accept_11_7_10_3_1_633 51 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 234 2 25 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 234 (accept_3_4 49 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 234 2 24 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 234 (Polychromatic418967fa.accept_23_1_3_4_1_7340 47 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 234 2 23 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 234 2 22 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 234 (accept_3_4 43 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 234 2 21 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 234 (Polychromatic418967fa.accept_17_7_11_13_1_2037 41 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 234 2 20 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 234 2 19 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 234 (accept_3_4 37 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 234 2 18 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 234 (Polychromatic418967fa.accept_15_5_14_9_1_274 35 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 234 2 17 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 234 2 16 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 234 (accept_3_4 31 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 234 2 15 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 234 2 14 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 234 2 13 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 234 (accept_3_4 25 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 234 2 12 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 234 (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 234 2 11 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 234 2 10 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 234 (accept_3_4 19 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 234 2 9 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 234 (Polychromatic418967fa.accept_19_17_12_6_1_8650 17 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 234 2 8 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 234 2 7 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 234 (accept_3_4 13 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 234 2 6 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 234 (Polychromatic418967fa.accept_22_11_10_14_1_9319 11 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 234 2 5 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 234 2 4 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 234 (accept_3_4 7 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  234 2 3 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 234 (Polychromatic418967fa.accept_15_5_14_9_1_274 5 164 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 234 2 2 82 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 164 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 234 2 1 82 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 234 (accept_3_4 1 164 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 163 234 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 163 234 (accept_3_5 71 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 163 234 (Polychromatic418967fa.accept_19_13_11_6_1_3128 70 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 163 234 (accept_3_5 68 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 163 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 67 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 163 234
  (Polychromatic418967fa.accept_31_4_8_17_1_14066 66 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 163 234 (accept_3_5 65 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 163 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 163 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 234 (Polychromatic418967fa.accept_15_3_13_9_1_3196 63 163
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 234 (accept_3_5 62 163
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3
  61 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 234
  (Polychromatic418967fa.accept_16_12_3_10_1_3524 60 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 163 234 (accept_3_5 59 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 163 234 (Polychromatic418967fa.accept_19_1_11_6_1_7152 58 163 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 234 (accept_3_5 56 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 234 (Polychromatic418967fa.accept_7_6_2_3_1_107
  55 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 234 (accept_3_5 53 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 234 (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 234 (Polychromatic418967fa.accept_19_13_11_6_1_3128 51 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 234 (accept_3_5 50 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 234 (accept_3_5 47 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 234 (Polychromatic418967fa.accept_25_21_13_9_1_14065 46 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 234 (accept_3_5 44 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 234
  (Polychromatic418967fa.accept_22_20_9_14_1_14004 42 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 163 234 (accept_3_5 41 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 163 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 163 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 234 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 163
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 234 (accept_3_5 38 163
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 234 (accept_3_5 35 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 234 (accept_3_5 32 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 234 (Polychromatic418967fa.accept_17_14_10_13_1_4147 31 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 234
  (Polychromatic418967fa.accept_21_9_16_3_1_11133 30 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 163 234 (accept_3_5 29 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 163 234 (Polychromatic418967fa.accept_11_6_9_3_1_1103 28 163 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 234 (accept_3_5 26 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 234
  (Polychromatic418967fa.accept_19_5_11_6_1_1909 24 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 234 (accept_3_5 23 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 234 (accept_3_5 20 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 234
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 18 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 234 (accept_3_5 17 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 234 (Polychromatic418967fa.accept_19_16_11_6_1_7149 16 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 234 (accept_3_5 14 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 234 (accept_3_5 11 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 234 (Polychromatic418967fa.accept_21_10_16_3_1_8047 10 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 234 (accept_3_5 8 163 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 234 (accept_3_5 5 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 234 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4 163 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 234 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 234 (accept_3_5 2 163 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 162 234 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 162 234 18 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 162 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 234 2 35 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 162 234 3 23 54 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 162 234 2 34 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 162 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 234 6 11 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 162 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 234 2 32 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 162 234 9 7 18 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 234 2 31 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 234 6 10 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 234 (Polychromatic418967fa.accept_15_14_12_9_1_3216 59 162 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 234 2 29 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 162 234 3 19 54 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 234 2 28 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 234
  (Polychromatic418967fa.accept_15_10_12_9_1_776 55 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 234 18 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 234 2 26 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 234 3 17 54 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 234 2 25 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 234
  (Polychromatic418967fa.accept_11_5_8_3_1_66 49 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 234 6 8 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 162 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 234 2 23 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 234 9 5 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 234 2 22 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 234
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 43 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 234 6 7 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 234 (Polychromatic418967fa.accept_29_12_17_2_1_14064 41 162 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 234 2 20 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 234 3 13 54 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 234 2 19 81 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 234 18 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 234 (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 234 2 17 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 234 3 11 54 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 234 2 16 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 234
  (Polychromatic418967fa.accept_19_12_10_6_1_8668 31 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 162 234 6 5 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 162 234 (Polychromatic418967fa.accept_15_14_12_9_1_3216 29 162 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 234 2 14 81 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 234 9 3 18 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 234 2 13 81 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 234 6 4 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 234 2 11 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 234 3 7 54 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 234 2 10 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 234 18 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 234 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 234 2 8 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 234 3 5 54 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 234 2 7 81 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 234
  (Polychromatic418967fa.accept_19_13_10_6_1_7147 13 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 234 6 2 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 162 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 234 2 5 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 234 9 1 18 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 234 2 4 81 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 234 6 1 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 162 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 234 2 2 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 234 3 1 54 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 234 2 1 81 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 234 (Polychromatic418967fa.accept_19_1_10_6_1_5726
  1 162 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 161 234 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 161 234 (accept_3_4 73 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 161 234 (Polychromatic418967fa.accept_17_4_8_13_1_7960 72 161 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 234 (accept_3_4 70 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 234
  (Polychromatic418967fa.accept_21_6_14_3_1_4932 69 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 161 234 (Polychromatic418967fa.accept_27_14_26_18_1_14063 68 161 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 234 (accept_3_4 67 161 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 234 (Polychromatic418967fa.accept_15_6_11_9_1_3215 66 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 234
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 161 234 (accept_3_4 64 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 161 234 (Polychromatic418967fa.accept_15_2_11_9_1_263 62 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 234 (accept_3_4 61 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 234 (Polychromatic418967fa.accept_14_4_7_10_1_3888 60 161
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 161 234 (accept_3_4 58 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 161 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 161 234 (Polychromatic418967fa.accept_17_5_8_13_1_7994 56 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 234 (accept_3_4 55 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 161 234 (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 161
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 234
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 53 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 161 234 (accept_3_4 52 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 161 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 234 (Polychromatic418967fa.accept_15_5_11_9_1_4276 50 161
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 234 (accept_3_4 49 161
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 161 234
  (Polychromatic418967fa.accept_11_4_7_3_1_289 48 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 234 (accept_3_4 46 161 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 161 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 234
  (Polychromatic418967fa.accept_21_2_14_3_1_4933 44 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 234 (accept_3_4 43 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 234 (Polychromatic418967fa.accept_22_20_7_14_1_7824 42 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 234 (Polychromatic418967fa.accept_16_9_1_10_1_3610 41 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 234 (accept_3_4 40 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 234
  (Polychromatic418967fa.accept_17_4_8_13_1_7960 38 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 234 (accept_3_4 37 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 234 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 234 (accept_3_4 34 161 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 234 (Polychromatic418967fa.accept_19_14_9_6_1_8633 33 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 234
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 234 (accept_3_4 31 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 234 (Polychromatic418967fa.accept_20_10_1_14_1_8359 30 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 234 (Polychromatic418967fa.accept_19_10_9_6_1_13992 29 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 234 (accept_3_4 28 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 234
  (Polychromatic418967fa.accept_11_4_7_3_1_289 26 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 234 (accept_3_4 25 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 234 (Polychromatic418967fa.accept_27_24_26_18_1_14062 24 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 234 (accept_3_4 22 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 234 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 161
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 234
  (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 234 (accept_3_4 19 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 234 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 234 (accept_3_4 16 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 234
  (Polychromatic418967fa.accept_19_14_9_6_1_8633 14 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 234 (accept_3_4 13 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 234 (Polychromatic418967fa.accept_21_12_14_3_1_12574 12 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 234 (accept_3_4 10 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 234 (Polychromatic418967fa.accept_16_9_1_10_1_3610 9 161
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 234
  (Polychromatic418967fa.accept_21_8_14_3_1_9602 8 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 234 (accept_3_4 7 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 234 (Polychromatic418967fa.accept_15_6_11_9_1_3215 6 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 234 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 161 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 234 (accept_3_4 4 161 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 234
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 234 (accept_3_4 1 161 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 160 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 160 234 2 37 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 160 234 (Polychromatic418967fa.accept_14_3_6_10_1_752 73 160 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 160 234 2 36 80 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 160 234 (accept_3_5 71 160 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 160 234 2 35 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 160 234
  (Polychromatic418967fa.accept_12_9_4_6_1_460 69 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 160 234 2 34 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 160 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 234 2 33 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 160 234 (accept_3_5 65 160 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 160 234 2 32 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 234 (Polychromatic418967fa.accept_11_8_6_3_1_661
  63 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 234 2 31 80 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 234
  (Polychromatic418967fa.accept_15_1_10_9_1_1495 61 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 160 234 2 30 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 160 234 (accept_3_5 59 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 160 234 2 29 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 160 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 234 2 28 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 234
  (Polychromatic418967fa.accept_19_17_8_6_1_7146 55 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 160 234 2 27 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 160 234 (accept_3_5 53 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 234 2 26 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 234 2 25 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 234
  (Polychromatic418967fa.accept_15_4_10_9_1_4298 49 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 234 2 24 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 234 (accept_3_5 47 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 234 2 23 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 234 2 22 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 234
  (Polychromatic418967fa.accept_24_19_16_18_1_14044 43 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 234 2 21 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 234 (accept_3_5 41 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 234 2 20 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 234 2 19 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 234 2 18 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 160 234 (accept_3_5 35 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 160 234 2 17 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 160 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 234 2 16 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 234
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 234 2 15 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 234 (accept_3_5 29 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 234 2 14 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 234 2 13 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 234 2 12 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 160 234 (accept_3_5 23 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 160 234 2 11 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 234 2 10 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 234
  (Polychromatic418967fa.accept_11_8_6_3_1_661 19 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 234 2 9 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 234 (accept_3_5 17 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 234 2 8 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 160 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 234 2 7 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 234
  (Polychromatic418967fa.accept_19_13_8_6_1_7195 13 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 234 2 6 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 160 234 (accept_3_5 11 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 234 2 5 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 234 2 4 80 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 234
  (Polychromatic418967fa.accept_19_7_8_6_1_3123 7 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 234 2 3 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 234 (accept_3_5 5 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  234 2 2 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 160 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 234 2 1 80 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 160 234 (Polychromatic418967fa.accept_15_1_10_9_1_1495 1 160 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 159 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 159 234 3 25 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 159 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 74 159 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 159 234 3 24 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 159 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 159 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 234 (Polychromatic418967fa.accept_12_10_3_6_1_882
  70 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 159 234 3 23 53 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 234
  (Polychromatic418967fa.accept_10_8_9_4_1_961 68 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 234 (Polychromatic418967fa.accept_21_4_12_3_1_12610 67 159 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 234 3 22 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 159 234 3 21 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 159 234 (Polychromatic418967fa.accept_12_2_3_6_1_112
  62 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 61 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 159 234 3 20 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 159 234 (Polychromatic418967fa.accept_16_11_15_10_1_3515 59 159 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 159 234 3 19 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 234 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 159 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420
  55 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 159 234 3 18 53 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 52 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 234 3 17 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 159 234 3 16 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 159 234 (Polychromatic418967fa.accept_22_3_5_14_1_14061 47 159 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 234 3 15 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 159 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 234 (Polychromatic418967fa.accept_7_1_5_3_1_268
  43 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 234 3 14 53 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 234 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 234 3 13 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 234 (Polychromatic418967fa.accept_10_8_9_4_1_961
  38 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 159 234 3 12 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 159 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 159 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 234
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 159 234 3 11 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 159 234 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 159 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 234
  (Polychromatic418967fa.accept_21_10_12_3_1_8076 31 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 159 234 3 10 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 159 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 234
  (Polychromatic418967fa.accept_10_8_9_4_1_961 28 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 159 234 3 9 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 159 234 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 234 3 8 53 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 234 3 7 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 234 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 234
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 159 234 3 6 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 159 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 234 3 5 53 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 234
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 234 3 4 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 234
  (Polychromatic418967fa.accept_16_11_15_10_1_3515 11 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 159 234 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 159 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 234 3 3 53 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 234 (Polychromatic418967fa.accept_17_7_6_13_1_10548 7 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 234 3 2 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 234
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 159 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 234 3 1 53 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 158 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 158 234 2 38 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 158 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 75 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 158 234 2 37 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 158 234 (accept_3_4 73 158 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 158 234 2 36 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 158 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 158 234 2 35 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 158 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 158 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 158 234 2 34 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 158 234 (accept_3_4 67 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 158 234 2 33 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 158 234
  (Polychromatic418967fa.accept_22_21_4_14_1_11011 65 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 158 234 2 32 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 158 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 158 234 2 31 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 158 234 (accept_3_4 61 158 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 158 234 2 30 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 158 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 59 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 158 234 2 29 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 158 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 158 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 158 234 2 28 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 158 234 (accept_3_4 55 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 158 234 2 27 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 158 234
  (Polychromatic418967fa.accept_16_5_14_10_1_3644 53 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 158 234 2 26 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 158 234 (Polychromatic418967fa.accept_11_7_4_3_1_302 51 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 158 234 2 25 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 158 234 (accept_3_4 49 158 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 158 234 2 24 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 158 234
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 47 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 158 234 2 23 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 158 234 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 158 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 158 234 2 22 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 158 234 (accept_3_4 43 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 158 234 2 21 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 158 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 234 2 20 79 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 234 2 19 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 234 (accept_3_4 37 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 234 2 18 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 234 (Polychromatic418967fa.accept_14_7_4_10_1_1351 35 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 234 2 17 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 234 2 16 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 234 (accept_3_4 31 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 234 2 15 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 158 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 234 2 14 79 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 234 2 13 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 234 (accept_3_4 25 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 234 2 12 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 234 (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 234 2 11 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 234
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 234 2 10 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 234 (accept_3_4 19 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 234 2 9 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 234 (Polychromatic418967fa.accept_15_2_8_9_1_4294 17 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 234 2 8 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 234 2 7 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 234 (accept_3_4 13 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 234 2 6 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 234 (Polychromatic418967fa.accept_23_11_20_4_1_14060 11 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 234 2 5 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 234 2 4 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 234 (accept_3_4 7 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  234 2 3 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 234 (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 158 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 234 2 2 79 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 234 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 158 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 234 2 1 79 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 234 (accept_3_4 1 158 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 157 234 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 157 234 (accept_3_5 77 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 157 234 (Polychromatic418967fa.accept_14_6_3_10_1_3905 76 157 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 157 234 (accept_3_5 74 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 157 234 (Polychromatic418967fa.accept_10_3_7_4_1_584
  73 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 157 234
  (Polychromatic418967fa.accept_10_2_7_4_1_967 72 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 157 234 (accept_3_5 71 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 234 (Polychromatic418967fa.accept_21_7_10_3_1_1049 70 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 234 (Polychromatic418967fa.accept_14_13_3_10_1_2159 69 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 234 (accept_3_5 68 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 234
  (Polychromatic418967fa.accept_23_20_19_4_1_14059 66 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 157 234 (accept_3_5 65 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 157 234 (Polychromatic418967fa.accept_19_7_5_6_1_9961 64 157 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 234 (accept_3_5 62 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 234 (Polychromatic418967fa.accept_10_1_7_4_1_968
  61 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 234
  (Polychromatic418967fa.accept_16_12_13_10_1_2637 60 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 157 234 (accept_3_5 59 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 157 234 (Polychromatic418967fa.accept_15_13_7_9_1_3210 58 157 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 234 (Polychromatic418967fa.accept_21_15_10_3_1_9578 57 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 234 (accept_3_5 56 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 157 234 (Polychromatic418967fa.accept_17_3_4_13_1_2030 54 157 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 234 (accept_3_5 53 157 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 157 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 234 (accept_3_5 50 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 234 (Polychromatic418967fa.accept_14_7_3_10_1_1364 49 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 234 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 234 (accept_3_5 47 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 234 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 234
  (Polychromatic418967fa.accept_19_7_5_6_1_9961 45 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 234 (accept_3_5 44 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 234 (accept_3_5 41 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 234 (Polychromatic418967fa.accept_27_13_22_18_1_6230 40
  157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 234 (accept_3_5 38 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 234 (Polychromatic418967fa.accept_16_5_13_10_1_3664 37 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 234 (Polychromatic418967fa.accept_21_15_10_3_1_9578 36 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 234 (accept_3_5 35 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 234 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 234
  (Polychromatic418967fa.accept_10_3_7_4_1_584 33 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 234 (accept_3_5 32 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 234 (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 234 (accept_3_5 29 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 234 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 234 (accept_3_5 26 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 234 (Polychromatic418967fa.accept_17_8_4_13_1_3014 25 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 234 (Polychromatic418967fa.accept_22_2_3_14_1_9314 24 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 234 (accept_3_5 23 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 234
  (Polychromatic418967fa.accept_10_1_7_4_1_968 21 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 234 (accept_3_5 20 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 234 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 234 (accept_3_5 17 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 234 (Polychromatic418967fa.accept_15_1_7_9_1_20 16 157 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 234 (accept_3_5 14 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 234 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 234 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 234 (accept_3_5 11 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 234 (Polychromatic418967fa.accept_25_10_7_9_1_14058 10 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 234
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 234 (accept_3_5 8 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 234 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 234 (accept_3_5 5 157 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 234 (Polychromatic418967fa.accept_19_4_5_6_1_11402 4 157
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 234 (accept_3_5 2 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 234 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 157 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 156 234 (Eq.refl Bool.true) (allA_succ_of_gcd 78 156 234 78 1 2 3 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 156 234
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 77 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 156 234 2 38 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 156 234 3 25 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 156 234 2 37 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 156 234
  (Polychromatic418967fa.accept_21_10_9_3_1_11127 73 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 156 234 6 12 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 156 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 156 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 234 2 35 78 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 156 234 3 23 52 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 234 2 34 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 234
  (Polychromatic418967fa.accept_11_1_2_3_1_688 67 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 234 6 11 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 156 234 13 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 156 234 2 32 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 156 234 3 21 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 234 2 31 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 234 6 10 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 234 (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 156 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 234 2 29 78 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 156 234 3 19 52 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 234 2 28 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 234 6 9 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 156 234 (Polychromatic418967fa.accept_16_5_12_10_1_3508 53 156 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 234 26 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 156 234 3 17 52 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 234 2 25 78 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 234
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 49 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 234 6 8 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 156 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 156 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 234 2 23 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 156 234 3 15 52 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 234 2 22 78 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 234 6 7 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 156 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 156 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 234 2 20 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 234 39 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 234 2 19 78 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 234
  (Polychromatic418967fa.accept_16_5_12_10_1_3508 37 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 156 234 6 6 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 156 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 156 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 234 2 17 78 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 234 3 11 52 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 234 2 16 78 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 234
  (Polychromatic418967fa.accept_15_1_6_9_1_254 31 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 234 6 5 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 156 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 234 2 14 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 234 3 9 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 234 26 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 234 (Polychromatic418967fa.accept_10_5_6_4_1_64 25
  156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 234 6 4 26 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 234
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 234 2 11 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 156 234 3 7 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 156 234 2 10 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 156 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 234 6 3 26 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 234
  (Polychromatic418967fa.accept_19_17_4_6_1_5810 17 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 234 2 8 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 156 234 3 5 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 156 234 2 7 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 13 156 234 13 1 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 156 234 6 2 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 234 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 156
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 234 2 5 78 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 156 234 3 3 52 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 234 2 4 78 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 234
  (Polychromatic418967fa.accept_21_7_9_3_1_8059 7 156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 234 6 1 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 234 2 2 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 234 3 1 52 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 234 2 1 78 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  156 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 155 234 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 155 234 (accept_3_4 79 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 155 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 78 155 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 234 (accept_3_4 76 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 234 (Polychromatic418967fa.accept_7_5_1_3_1_103
  75 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 74 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 234 (accept_3_4 73 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 234 (Polychromatic418967fa.accept_10_1_5_4_1_276 71 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 234 (accept_3_4 70 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 68 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 234 (accept_3_4 67 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 234 (accept_3_4 64 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 63 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 234
  (Polychromatic418967fa.accept_19_5_3_6_1_8642 62 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 234 (accept_3_4 61 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 234 (Polychromatic418967fa.accept_10_9_5_4_1_966 59 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 234 (accept_3_4 58 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 234
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 234 (accept_3_4 55 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 234 (accept_3_4 52 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 234
  (Polychromatic418967fa.accept_20_10_15_14_1_6797 50 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 155 234 (accept_3_4 49 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 48 155 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 234 (accept_3_4 46 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 234 (accept_3_4 43 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 234 (Polychromatic418967fa.accept_15_12_5_9_1_3234 42 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 234 (accept_3_4 40 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 234
  (Polychromatic418967fa.accept_21_17_8_3_1_9576 38 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 234 (accept_3_4 37 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 234 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 234 (accept_3_4 34 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 234 (accept_3_4 31 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 234 (accept_3_4 28 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 234 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 234 (accept_3_4 25 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 234 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 234 (accept_3_4 22 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 234
  (Polychromatic418967fa.accept_19_1_3_6_1_5827 20 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 234 (accept_3_4 19 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 234 (accept_3_4 16 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 234 (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 155 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 234
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 234 (accept_3_4 13 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 234 (accept_3_4 10 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 234
  (Polychromatic418967fa.accept_19_8_3_6_1_9982 8 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 234 (accept_3_4 7 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 234 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 234 (accept_3_4 4 155 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 234 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 155 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 234 (accept_3_4 1 155 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 154 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 154 234 2 40 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 154 234 (Polychromatic418967fa.accept_19_3_2_6_1_11398 79 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 154 234 2 39 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 154 234 (accept_3_5 77 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 154 234 2 38 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 154 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 75 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 154 234 2 37 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 154 234 (Polychromatic418967fa.accept_15_13_4_9_1_2283 73 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 154 234 2 36 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 154 234 (accept_3_5 71 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 154 234 2 35 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 154 234
  (Polychromatic418967fa.accept_12_9_10_6_1_872 69 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 154 234 2 34 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 154 234 (Polychromatic418967fa.accept_19_10_2_6_1_5731 67 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 154 234 2 33 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 154 234 (accept_3_5 65 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 154 234 2 32 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 154 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 154 234 2 31 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 154 234 (Polychromatic418967fa.accept_19_4_2_6_1_7181 61 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 154 234 2 30 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 154 234 (accept_3_5 59 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 154 234 2 29 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 154 234
  (Polychromatic418967fa.accept_12_9_10_6_1_872 57 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 154 234 2 28 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 154 234 (Polychromatic418967fa.accept_15_10_4_9_1_3203 55 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 154 234 2 27 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 234 (accept_3_5 53 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 234 2 26 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 51 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 154 234 2 25 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 154 234 (Polychromatic418967fa.accept_28_21_14_10_1_14057 49 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 154 234 2 24 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 234 (accept_3_5 47 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 154 234 2 23 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 154 234
  (Polychromatic418967fa.accept_12_9_10_6_1_872 45 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 154 234 2 22 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 154 234 (Polychromatic418967fa.accept_15_13_4_9_1_2283 43 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 154 234 2 21 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 154 234 (accept_3_5 41 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 154 234 2 20 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 154 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 39 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 154 234 2 19 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 154 234 (Polychromatic418967fa.accept_21_16_7_3_1_8093 37 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 154 234 2 18 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 154 234 (accept_3_5 35 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 154 234 2 17 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 154 234
  (Polychromatic418967fa.accept_12_9_10_6_1_872 33 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 154 234 2 16 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 154 234 (Polychromatic418967fa.accept_17_14_1_13_1_12898 31 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 154 234 2 15 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 154 234 (accept_3_5 29 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 154 234 2 14 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 154 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 154 234 2 13 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 154 234 (Polychromatic418967fa.accept_15_10_4_9_1_3203 25 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 154 234 2 12 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 154 234 (accept_3_5 23 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 234 2 11 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 154 234
  (Polychromatic418967fa.accept_12_9_10_6_1_872 21 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 154 234 2 10 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 154 234 (Polychromatic418967fa.accept_17_2_1_13_1_6670 19 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 234 2 9 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 234 (accept_3_5 17 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 234 2 8 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 234
  (Polychromatic418967fa.accept_12_3_10_6_1_442 15 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 154 234 2 7 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 154 234 (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 154 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 234 2 6 77 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 234 (accept_3_5 11 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 234 2 5 77 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 234
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 234 2 4 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 234 (Polychromatic418967fa.accept_23_7_16_4_1_12508 7 154 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 234 2 3 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 234 (accept_3_5 5 154 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154 234 2 2 77 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 154 234 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 154 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 234 2 1 77 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 234
  (Polychromatic418967fa.accept_19_1_2_6_1_4411 1 154 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 154 234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 153
  234 (Eq.refl Bool.true) (allA_succ_of_gcd 81 153 234 9 9 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 153 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 80 153 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 153 234 3 26 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 153 234 (Polychromatic418967fa.accept_10_7_3_4_1_978 77 153 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 234 (Polychromatic418967fa.accept_12_4_9_6_1_440
  76 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 153 234 3 25 51 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 153 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 234 (Polychromatic418967fa.accept_11_7_10_3_1_633 73 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 153 234 9 8 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 71
  153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 234
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 153 234 3 23 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 153 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 68 153 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 153 234 3 22 51 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 153 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 153 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 64 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 153 234 9 7 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 153 234 (Polychromatic418967fa.accept_11_7_10_3_1_633
  62 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 234
  (Polychromatic418967fa.accept_20_1_13_14_1_1481 61 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 153 234 3 20 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 153 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 58 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 234 3 19 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 153 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 153 234 9 6 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 153 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 53 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 153 234 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 234 3 17 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 234 (Polychromatic418967fa.accept_12_2_9_6_1_439
  50 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 234
  (Polychromatic418967fa.accept_10_9_3_4_1_985 49 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 153 234 3 16 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 234 (Polychromatic418967fa.accept_7_4_6_3_1_271
  46 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 234 9 5 17 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 234
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 234 3 14 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 234 (Polychromatic418967fa.accept_19_3_1_6_1_3114
  41 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 234
  (Polychromatic418967fa.accept_11_7_10_3_1_633 40 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 153 234 3 13 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 153 234 (Polychromatic418967fa.accept_12_2_9_6_1_439 38 153 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 234 (Polychromatic418967fa.accept_7_2_6_3_1_100
  37 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 234 9 4 17 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 234 (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 234 3 11 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 32
  153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 234
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 234 3 10 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 234 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 153 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 234 (Polychromatic418967fa.accept_12_4_9_6_1_440
  28 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 234 9 3 17 26
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 234
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 234 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 234 3 8 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 234
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 234 3 7 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 234 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 234 9 2 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 234
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 234 3 5 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 234 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 234
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 234 3 4 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 234 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 153
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 234 9 1 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 234
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 234 3 2 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 234 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 153 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 234
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 234 3 1 51 78 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 234 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 153 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 234 (Polychromatic418967fa.accept_16_1_9_10_1_4740 1 153
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 152 234 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 152 234 2 41 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 152 234 (Polychromatic418967fa.accept_12_9_8_6_1_466 81 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 152 234 2 40 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 152 234 (accept_3_4 79 152 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 152 234 2 39 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 152 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 77 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 152 234 2 38 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 152 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 75 152 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 152 234 2 37 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 152 234 (accept_3_4 73 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 152 234 2 36 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 152 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 71
  152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 234 2 35 76 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 69 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 234 2 34 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 234 (accept_3_4 67 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 234 2 33 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 152 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 234 2 32 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 234
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 234 2 31 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 234 (accept_3_4 61 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 234 2 30 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 234 (Polychromatic418967fa.accept_23_13_14_4_1_12470 59 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 234 2 29 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 234 2 28 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 234 (accept_3_4 55 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 234 2 27 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 234 (Polychromatic418967fa.accept_15_8_2_9_1_3200 53 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 234 2 26 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 234 2 25 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 234 (accept_3_4 49 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 234 2 24 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 234 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 152 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 234 2 23 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 234 2 22 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 234 (accept_3_4 43 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 234 2 21 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 234 (Polychromatic418967fa.accept_15_11_2_9_1_1480 41 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 234 2 20 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 234
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 39 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 234 2 19 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 234 (accept_3_4 37 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 234 2 18 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 234 (Polychromatic418967fa.accept_24_11_8_18_1_14056 35 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 234 2 17 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 234 2 16 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 234 (accept_3_4 31 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 234 2 15 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 234 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 152 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 234 2 14 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 234
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 234 2 13 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 234 (accept_3_4 25 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 234 2 12 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 234 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 152 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 234 2 11 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 234
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 234 2 10 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 234 (accept_3_4 19 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 234 2 9 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 234 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 152 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 234 2 8 76 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 234
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 234 2 7 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 234 (accept_3_4 13 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 234 2 6 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 234 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 234 2 5 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 234
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 234 2 4 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 234 (accept_3_4 7 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  234 2 3 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 234 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 152 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 234 2 2 76 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 234 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 152 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 234 2 1 76 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 234 (accept_3_4 1 152 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 151 234 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 151 234 (accept_3_5 83 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 151 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 82 151 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 151 234 (accept_3_5 80 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 151 234
  (Polychromatic418967fa.accept_17_11_15_13_1_11717 79 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 151 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 151 234 (accept_3_5 77 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 234
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 234 (accept_3_5 74 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 234 (accept_3_5 71 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 234 (Polychromatic418967fa.accept_15_10_1_9_1_5356 70 151
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 234
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 234 (accept_3_5 68 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447 67 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 234 (Polychromatic418967fa.accept_15_6_1_9_1_1476 66 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 234 (accept_3_5 65 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 234
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 63 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 151 234 (accept_3_5 62 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 151 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 234 (accept_3_5 59 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 234
  (Polychromatic418967fa.accept_19_1_18_6_1_3110 58 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 151 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 234 (accept_3_5 56 151 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 151 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 234
  (Polychromatic418967fa.accept_21_12_4_3_1_4924 54 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 234 (accept_3_5 53 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 234 (Polychromatic418967fa.accept_15_7_1_9_1_1500 52 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 234 (Polychromatic418967fa.accept_15_6_1_9_1_1476 51 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 234 (accept_3_5 50 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 234 (accept_3_5 47 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 234 (Polychromatic418967fa.accept_16_14_7_10_1_898 46 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 234 (accept_3_5 44 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 234
  (Polychromatic418967fa.accept_17_8_15_13_1_7942 42 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 151 234 (accept_3_5 41 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 151 234 (Polychromatic418967fa.accept_15_10_1_9_1_5356 40 151 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 151
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 234 (accept_3_5 38 151
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 234
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 234 (accept_3_5 35 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 234 (accept_3_5 32 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 234 (Polychromatic418967fa.accept_19_12_18_6_1_14021 31 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 234
  (Polychromatic418967fa.accept_16_14_7_10_1_898 30 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 234 (accept_3_5 29 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 234 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 234 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 234 (accept_3_5 26 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 234
  (Polychromatic418967fa.accept_19_5_18_6_1_7191 24 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 234 (accept_3_5 23 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 234 (accept_3_5 20 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 234 (Polychromatic418967fa.accept_16_3_7_10_1_3503 19 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 234
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 18 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 234 (accept_3_5 17 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 234 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 234 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 234 (accept_3_5 14 151 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 234
  (Polychromatic418967fa.accept_19_12_18_6_1_14021 12 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 151 234 (accept_3_5 11 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 151 234 (Polychromatic418967fa.accept_15_10_1_9_1_5356 10 151 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 234 (accept_3_5 8 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 234 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  7 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 234
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 234 (accept_3_5 5 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 234 (Polychromatic418967fa.accept_29_4_6_2_1_14055 4 151 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 234 (Polychromatic418967fa.accept_16_3_7_10_1_3503 3 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 234 (accept_3_5 2 151 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 234 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 150 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 150 234 6 14 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 150 234 (Polychromatic418967fa.accept_24_11_6_18_1_10695 83 150
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 234 2 41 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 150 234 3 27 50 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 150 234 2 40 75
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 150 234
  (Polychromatic418967fa.accept_19_3_17_6_1_1991 79 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 234 6 13 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 234 (Polychromatic418967fa.accept_23_8_12_4_1_12469 77 150 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 234 2 38 75 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 150 234 3 25 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 234 2 37 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 234
  (Polychromatic418967fa.accept_22_7_18_14_1_7813 73 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 150 234 6 12 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 150 234 (Polychromatic418967fa.accept_20_11_10_14_1_13955 71 150 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 234 2 35 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 150 234 3 23 50 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 234 2 34 75
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 234
  (Polychromatic418967fa.accept_22_1_18_14_1_12549 67 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 150 234 6 11 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 150 234 (Polychromatic418967fa.accept_11_10_7_3_1_3679 65 150 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 234 2 32 75 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 150 234 3 21 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 234 2 31 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 234
  (Polychromatic418967fa.accept_17_10_14_13_1_12880 61 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 150 234 6 10 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 150 234 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 150 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 234 2 29 75 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 150 234 3 19 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 234 2 28 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 234
  (Polychromatic418967fa.accept_17_4_14_13_1_3072 55 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 150 234 6 9 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 150 234 (Polychromatic418967fa.accept_24_5_6_18_1_14054 53 150 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 234 2 26 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 150 234 3 17 50 78
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 234 2 25 75
  117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 234
  (Polychromatic418967fa.accept_19_11_17_6_1_7157 49 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 150 234 6 8 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 150 234 (Polychromatic418967fa.accept_19_9_17_6_1_3108 47 150 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 234 2 23 75 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 234 3 15 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 234 2 22 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 234
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 234 6 7 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 150 234 (Polychromatic418967fa.accept_19_3_17_6_1_1991 41 150 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 234 2 20 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 234 3 13 50 78 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 234 2 19 75 117 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 234
  (Polychromatic418967fa.accept_11_4_7_3_1_289 37 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 234 6 6 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 150 234 (Polychromatic418967fa.accept_17_1_14_13_1_7966 35 150 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 234 2 17 75 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 234 3 11 50 78 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 234 2 16 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 234
  (Polychromatic418967fa.accept_19_12_17_6_1_11365 31 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 234 6 5 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 234 (Polychromatic418967fa.accept_22_7_18_14_1_7813 29 150 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 234 2 14 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 234 3 9 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 234 2 13 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 234
  (Polychromatic418967fa.accept_20_5_10_14_1_5317 25 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 150 234 6 4 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 234 (Polychromatic418967fa.accept_19_4_17_6_1_12656 23 150 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 234 2 11 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 234 3 7 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 234 2 10 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 234
  (Polychromatic418967fa.accept_24_19_6_18_1_8966 19 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 150 234 6 3 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 150 234 (Polychromatic418967fa.accept_24_17_6_18_1_12333 17 150 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 234 2 8 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 234 3 5 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 234 2 7 75 117
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 234
  (Polychromatic418967fa.accept_19_13_17_6_1_11363 13 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 150 234 6 2 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 150 234 (Polychromatic418967fa.accept_19_11_17_6_1_7157 11 150 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 234 2 5 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 234 3 3 50 78 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 234 2 4 75 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 234
  (Polychromatic418967fa.accept_22_7_18_14_1_7813 7 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 234 6 1 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 234 (Polychromatic418967fa.accept_20_5_10_14_1_5317 5 150 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 234 2 2 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 234 3 1 50 78 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 234 2 1 75 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 234 (Polychromatic418967fa.accept_17_1_14_13_1_7966
  1 150 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  234))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 149 234
  (Eq.refl Bool.true) (allA_succ_of_accept 85 149 234 (accept_3_4 85 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 149 234 (Polychromatic418967fa.accept_19_8_16_6_1_5804 84 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 234 (accept_3_4 82 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 234
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 81 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 149 234 (Polychromatic418967fa.accept_15_5_14_9_1_274 80 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 234 (accept_3_4 79 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 149 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 234
  (Polychromatic418967fa.accept_16_13_5_10_1_1680 77 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 149 234 (accept_3_4 76 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 74 149
  234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 234 (accept_3_4 73 149
  234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 234
  (Polychromatic418967fa.accept_15_12_14_9_1_778 72 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 234 (accept_3_4 70 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 149 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 234 (Polychromatic418967fa.accept_7_5_2_3_1_106
  68 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 234 (accept_3_4 67
  149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 234
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 66 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 149 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420 65 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 234 (accept_3_4 64 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 234 (Polychromatic418967fa.accept_7_6_2_3_1_107
  62 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 234 (accept_3_4 61
  149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 234
  (Polychromatic418967fa.accept_16_12_5_10_1_3561 60 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 234 (accept_3_4 58 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 234
  (Polychromatic418967fa.accept_21_14_2_3_1_8019 56 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 234 (accept_3_4 55 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 234 (Polychromatic418967fa.accept_10_3_9_4_1_960 53 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 234 (accept_3_4 52 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 234 (accept_3_4 49 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 234 (accept_3_4 46 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 234 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 234
  (Polychromatic418967fa.accept_16_12_5_10_1_3561 44 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 149 234 (accept_3_4 43 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 149 234 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 234 (accept_3_4 40 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 234
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 234 (accept_3_4 37 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 234 (accept_3_4 34 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 234
  (Polychromatic418967fa.accept_27_5_14_18_1_14034 32 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 149 234 (accept_3_4 31 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 149 234 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 234 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 234 (accept_3_4 28 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 234
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 234 (accept_3_4 25 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 234 (Polychromatic418967fa.accept_20_4_9_14_1_5316 24 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 234 (accept_3_4 22 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 234 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 234
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 234 (accept_3_4 19 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 234 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 234 (Polychromatic418967fa.accept_21_17_2_3_1_4942 17 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 234 (accept_3_4 16 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 234
  (Polychromatic418967fa.accept_16_14_5_10_1_3622 14 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 149 234 (accept_3_4 13 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 149 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 234 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 234 (accept_3_4 10 149 234
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 234 (Polychromatic418967fa.accept_11_9_6_3_1_1668
  9 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 234
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 234 (accept_3_4 7 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 234 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 234 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 234 (accept_3_4 4 149 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 234 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 234
  (Polychromatic418967fa.accept_23_2_11_4_1_14053 2 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 234 (accept_3_4 1 149 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 148 234
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 148 234 2 43 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 148 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 85 148 234
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 148 234 2 42 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 148 234 (accept_3_5 83
  148 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 148 234 2 41 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 148 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 148 234 2 40 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 148 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 148 234 2 39 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 148 234 (accept_3_5 77 148 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 148 234 2 38 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 148 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 148 234 2 37 74 117 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 148 234
  (Polychromatic418967fa.accept_19_16_15_6_1_12661 73 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 148 234 2 36 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 148 234 (accept_3_5 71 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 234 2 35 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 234 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 234 2 34 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 234 2 33 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 234 (accept_3_5 65 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 234 2 32 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 234 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 234 2 31 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 234 2 30 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 234 (accept_3_5 59 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 234 2 29 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 234 2 28 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 234
  (Polychromatic418967fa.accept_20_15_8_14_1_14036 55 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 148 234 2 27 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 148 234 (accept_3_5 53 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 234 2 26 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 234 2 25 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 234
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 234 2 24 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 234 (accept_3_5 47 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 234 2 23 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 234 2 22 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 234
  (Polychromatic418967fa.accept_19_5_15_6_1_1986 43 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 234 2 21 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 234 (accept_3_5 41 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 234 2 20 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 234 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 234 2 19 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 234
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 234 2 18 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 234 (accept_3_5 35 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 234 2 17 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 234 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 234 2 16 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 234
  (Polychromatic418967fa.accept_19_12_15_6_1_7138 31 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 148 234 2 15 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 148 234 (accept_3_5 29 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 234 2 14 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 234 2 13 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 234
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 234 2 12 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 234 (accept_3_5 23 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 234 2 11 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 234 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 234 2 10 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 234
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 234 2 9 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 234 (accept_3_5 17 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 234 2 8 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 148 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 234 2 7 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 234
  (Polychromatic418967fa.accept_19_13_15_6_1_7131 13 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 148 234 2 6 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 148 234 (accept_3_5 11 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 234 2 5 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 234 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 234 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 234 2 4 74 117 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 234
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 234 2 3 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 234 (accept_3_5 5 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  234 2 2 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 234 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 148 234 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 234 2 1 74 117 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 148 234 (Polychromatic418967fa.accept_17_1_12_13_1_448 1 148 234 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  234)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_234_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


