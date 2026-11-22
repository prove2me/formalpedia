-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch228
-- name    : Polychromatic418967fa_Branch228
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:25:47.481017+00:00
-- url     : https://prove2.me/theorems/c6d89010-4637-4659-abbf-c410b2faa9b0
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch228_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_228 : allB 228 228 :=
  allB_succ' 2 227 228 (Eq.refl Bool.true) (allA_succ_of_accept 1 227 228 (accept_3_4 1 227 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 228)) (allB_succ' 3 226 228 (Eq.refl Bool.true) (allA_succ_of_gcd 2 226 228 2 1 113
  114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 228
  (Polychromatic418967fa.accept_27_1_10_12_1_2166 1 226 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 228))) (allB_succ' 4 225 228 (Eq.refl Bool.true) (allA_succ_of_gcd 3 225 228 3 1 75 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 228
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 225 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 228 (Polychromatic418967fa.accept_21_1_15_18_1_7646 1 225 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 228)))) (allB_succ' 5 224 228 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  224 228 4 1 56 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 224 228 (Polychromatic418967fa.accept_18_3_8_12_1_3283 3 224 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 224 228 2 1 112 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 224 228 (accept_3_4 1 224 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 224 228))))) (allB_succ' 6 223 228 (Eq.refl Bool.true) (allA_succ_of_accept 5 223 228 (accept_3_5 5 223 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 4
  223 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 223 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 228 (accept_3_5 2 223 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 223 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 228)))))) (allB_succ' 7 222 228 (Eq.refl Bool.true) (allA_succ_of_gcd 6 222 228 6 1 37 38
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 222 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 228 2 2 111 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 222 228 3 1 74 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 222 228 2 1 111 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 222 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 222 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 228))))))) (allB_succ' 8 221 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 221 228 (accept_3_4 7 221 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 221 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 228 (Polychromatic418967fa.accept_21_5_11_18_1_1789 5 221 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 228 (accept_3_4 4 221 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 228 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 221 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 221 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 228 (accept_3_4 1 221 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  228)))))))) (allB_succ' 9 220 228 (Eq.refl Bool.true) (allA_succ_of_gcd 8 220 228 4 2 55 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 228
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 220 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 220 228 2 3 110 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 220 228 (accept_3_5 5 220 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 220 228 4 1 55 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 220 228 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 220 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 228 2 1 110 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 1
  220 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 228))))))))) (allB_succ' 10 219 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 219 228 3 3 73 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 8 219 228 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 219 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 228
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 219 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 219 228 3 2 73 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 219 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 219 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 228 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 219 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 219 228 3 1 73 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 219 228
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 219 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 228 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 219 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 228)))))))))) (allB_succ' 11 218 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 218 228 2 5 109 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 218 228 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 218 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 218 228 2 4 109 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 218 228 (accept_3_4 7 218 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 218 228 2 3 109 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 218 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  218 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 228 2 2 109 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 218 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 228 2 1 109 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 228 (accept_3_4 1 218 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  228))))))))))) (allB_succ' 12 217 228 (Eq.refl Bool.true) (allA_succ_of_accept 11 217 228 (accept_3_5 11 217 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 228
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 217 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 217 228 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 217 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 228 (accept_3_5 8 217 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 217 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 217 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  217 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 228 (accept_3_5 5 217
  228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 228
  (Polychromatic418967fa.accept_9_4_1_3_1_190 4 217 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 217 228 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 217 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 228 (accept_3_5 2 217 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 217 228 (Polychromatic418967fa.accept_25_1_17_3_1_13656 1 217 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 228)))))))))))) (allB_succ' 13 216 228 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 216 228 12 1 18 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 216 228 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 216 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 228 2 5 108 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 216 228 3 3 72 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 216 228 4 2 54 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 228
  (Polychromatic418967fa.accept_16_7_8_4_1_689 7 216 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 228 6 1 36 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 216 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 228 4 1 54 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 216 228 3 1 72 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 216 228 2 1 108 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 228 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1
  216 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 228))))))))))))) (allB_succ' 14 215
  228 (Eq.refl Bool.true) (allA_succ_of_accept 13 215 228 (accept_3_4 13 215 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 215 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 215 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 215 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 228 (accept_3_4 10 215 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 215 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 215 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 228 (accept_3_4 7 215 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 215 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 215 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 228 (accept_3_4 4 215 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 215 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 215 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 228 (accept_3_4 1 215 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 228)))))))))))))) (allB_succ' 15 214 228 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  214 228 2 7 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 214 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 214 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 214 228 2 6 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 214 228 (accept_3_5 11 214 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 214 228 2 5 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 214 228 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 214 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 228 2 4 107 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 228
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 214 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 228 2 3 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 228 (accept_3_5 5 214 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 228 2 2 107 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 228 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 214 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 228 2 1 107 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 228
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 214 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 228))))))))))))))) (allB_succ' 16 213 228 (Eq.refl Bool.true) (allA_succ_of_gcd 15 213 228 3 5 71 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 213 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 213 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 213 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 228 3 4 71 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  213 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 213 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 213 228 3 3 71 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 213 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 213 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 213 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 213 228 3 2 71 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 213 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 213 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 213 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 228 3 1 71 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 213 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 213 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 213 228)))))))))))))))) (allB_succ' 17 212 228 (Eq.refl Bool.true) (allA_succ_of_gcd 16 212 228 4 4 53 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 228
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 212 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 228 2 7 106 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 228 (accept_3_4 13 212 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 228 4 3 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 212 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 212 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 228 2 5 106 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 228 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9
  212 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 228 4 2 53 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 228 (accept_3_4 7
  212 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 228 2 3 106 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 212 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 212 228 4 1 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 212 228 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 212 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 228 2 1 106 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 228 (accept_3_4 1 212 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 228))))))))))))))))) (allB_succ' 18 211 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 211 228 (accept_3_5 17 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 211 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 228 (accept_3_5 14 211 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 228 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 211 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 228 (accept_3_5 11 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 228 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 211 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 228 (accept_3_5 8 211 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 211 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 228 (accept_3_5 5 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 228 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 211 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 211 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 228 (accept_3_5 2 211 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 211 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 228)))))))))))))))))) (allB_succ' 19 210 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 210 228 6 3 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 210 228 (Polychromatic418967fa.accept_20_17_10_8_1_9374 17 210 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 228 2 8 105 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 210 228 3 5 70 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 228 2 7 105 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 228
  (Polychromatic418967fa.accept_17_13_6_7_1_4999 13 210 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 228 6 2 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 210 228 (Polychromatic418967fa.accept_22_11_12_8_1_13645 11 210 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 228 2 5 105 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 228 3 3 70 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 228 2 4 105 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 228
  (Polychromatic418967fa.accept_20_7_10_8_1_9411 7 210 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 228 6 1 35 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 210 228 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 210 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 228 2 2 105 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 228 3 1 70 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 228 2 1 105 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 228
  (Polychromatic418967fa.accept_22_1_12_8_1_10601 1 210 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 228))))))))))))))))))) (allB_succ' 20 209 228 (Eq.refl Bool.true) (allA_succ_of_gcd 19 209 228 19 1 11
  12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 209 228
  (Polychromatic418967fa.accept_24_18_17_12_1_3252 18 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 209 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 228 (accept_3_4 16 209 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 209 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 228 (accept_3_4 13 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 228 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 209 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 228 (accept_3_4 10 209 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 209 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 228 (accept_3_4 7 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 228 (accept_3_4 4 209 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 209 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 228 (accept_3_4 1 209 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  228)))))))))))))))))))) (allB_succ' 21 208 228 (Eq.refl Bool.true) (allA_succ_of_gcd 20 208 228 4 5 52 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 228
  (Polychromatic418967fa.accept_22_19_10_8_1_9011 19 208 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 208 228 2 9 104 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 208 228 (accept_3_5 17 208 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 228 4 4 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 208 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 208 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 228 2 7 104 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  208 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 208 228 4 3 52 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 228 (accept_3_5 11
  208 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 228 2 5 104 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 208 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 208 228 4 2 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 208 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 208 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 228 2 3 104 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 228 (accept_3_5 5 208 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 228 4 1 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 208 228 (Polychromatic418967fa.accept_17_3_4_7_1_1658 3 208 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 228 2 1 104 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 208 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 228))))))))))))))))))))) (allB_succ' 22 207 228 (Eq.refl Bool.true) (allA_succ_of_gcd 21 207 228 3 7 69
  76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 228
  (Polychromatic418967fa.accept_25_20_7_3_1_13655 20 207 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 207 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 207 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 228 3 6 69 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 228
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 207 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 228 (Polychromatic418967fa.accept_17_16_3_7_1_5028 16 207 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 228 3 5 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 228
  (Polychromatic418967fa.accept_16_14_15_4_1_3268 14 207 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 207 228 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 207 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 228 3 4 69 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 207 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 228 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 207 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 207 228 3 3 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 207 228 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 207 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 228
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 207 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 207 228 3 2 69 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 207 228 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 207 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 228 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 207
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 228 3 1 69 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 228
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 207 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 228 (Polychromatic418967fa.accept_14_1_11_4_1_3430 1 207 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 228)))))))))))))))))))))) (allB_succ' 23 206 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 206 228 2 11 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 206 228 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 206 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 206 228 2 10 103 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 206 228 (accept_3_4 19 206 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 206 228 2 9 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 206 228
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 206 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 206 228 2 8 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 206 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 206 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 206 228 2 7 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 206 228 (accept_3_4 13 206 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 206 228 2 6 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 206 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 11
  206 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 228 2 5 103 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 228
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 206 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 228 2 4 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 228 (accept_3_4 7 206 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 228 2 3 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 206 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 228 2 2 103 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 228
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 206 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 228 2 1 103 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 228 (accept_3_4 1 206 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  228))))))))))))))))))))))) (allB_succ' 24 205 228 (Eq.refl Bool.true) (allA_succ_of_accept 23 205 228 (accept_3_5 23
  205 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 228
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 205 228 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 205 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 228 (accept_3_5 20 205 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 205 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 205 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 228
  (Polychromatic418967fa.accept_22_18_7_8_1_12020 18 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 205 228 (accept_3_5 17 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 205 228 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 205 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 205 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 228 (accept_3_5 14 205 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 228 (Polychromatic418967fa.accept_7_6_2_4_1_291
  13 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 228 (accept_3_5 11 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 205 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 228 (accept_3_5 8 205 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 228 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 205 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 228 (accept_3_5 5 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 205 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 228 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 205 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 228 (accept_3_5 2 205 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 205 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 228)))))))))))))))))))))))) (allB_succ' 25 204 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 204 228 12 2 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 204 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 228 2 11 102 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 204 228 3 7 68 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 228 4 5 51 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 204 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 228 6 3 34 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 204 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 228 4 4 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 204 228 3 5 68 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 204 228 2 7 102 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 204 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 228 12 1 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 204 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 228 2 5 102 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 228 3 3 68 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 228 4 2 51 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 204 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 228 6 1 34 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 204 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 228 4 1 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 228 3 1 68 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 228 2 1 102 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 1
  204 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 228)))))))))))))))))))))))))
  (allB_succ' 26 203 228 (Eq.refl Bool.true) (allA_succ_of_accept 25 203 228 (accept_3_4 25 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 203 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 228
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 228 (accept_3_4 22 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 228 (accept_3_4 19 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 228 (Polychromatic418967fa.accept_20_18_3_8_1_7903 18 203 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 228
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 228 (accept_3_4 16 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 228 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 203 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 228 (accept_3_4 13 203 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 228 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 203
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 228 (accept_3_4 10 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 228 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 228 (accept_3_4 7 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 203 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 228
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 228 (accept_3_4 4 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 228 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 203 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 228 (accept_3_4 1 203 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 228)))))))))))))))))))))))))) (allB_succ' 27 202 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 202 228 2 13 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 202 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 202 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 202 228 2 12 101 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 202 228 (accept_3_5 23 202 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 202 228 2 11 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 202 228
  (Polychromatic418967fa.accept_22_21_4_8_1_12043 21 202 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 202 228 2 10 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 202 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 202 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 202 228 2 9 101 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 202 228 (accept_3_5 17 202 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 202 228 2 8 101 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 202 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 202 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 202 228 2 7 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 202 228 (Polychromatic418967fa.accept_36_13_22_12_1_13654 13 202 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 202 228 2 6 101 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 202 228 (accept_3_5 11 202 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 202 228 2 5 101 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 202 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 202 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 202 228 2 4 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 202 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 202 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 202 228 2 3 101 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 202 228 (accept_3_5 5 202 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 202 228 2 2 101 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 202 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  202 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 228 2 1 101 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 228
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 202 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 228))))))))))))))))))))))))))) (allB_succ' 28 201 228 (Eq.refl Bool.true) (allA_succ_of_gcd 27 201 228 3
  9 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201
  228 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 201 228 (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 201 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 201 228 3 8 67 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 201 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 201 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 228 3 7 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 228
  (Polychromatic418967fa.accept_10_9_1_8_1_755 19 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 201 228 3 6 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 201 228 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 201 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 201 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 201 228 3 5 67 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 228
  (Polychromatic418967fa.accept_13_1_6_7_1_550 14 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 201 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 228 3 4 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 228 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  11 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 228
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 201 228 3 3 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 201 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 201 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 228 (Polychromatic418967fa.accept_18_7_3_12_1_3241 7 201
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 228 3 2 67 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 228
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 228 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 201 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 228 3 1 67 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 201 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 201 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 201 228)))))))))))))))))))))))))))) (allB_succ' 29 200 228 (Eq.refl Bool.true) (allA_succ_of_gcd 28 200 228
  4 7 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200
  228 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 200 228 2 13 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 200 228 (accept_3_4 25 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 228 4 6 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 200 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 200 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 228 2 11 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 228 (Polychromatic418967fa.accept_15_6_5_3_1_1988
  21 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 228 4 5 50 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 228
  (accept_3_4 19 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 228 2 9 100 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 200 228 4 4 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 200 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 200 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 228 2 7 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 228 (accept_3_4 13 200 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 228 4 3 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 228 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 200
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 228 2 5 100 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 228
  (Polychromatic418967fa.accept_15_9_5_3_1_554 9 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 228 4 2 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 200 228 (accept_3_4 7 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200
  228 2 3 100 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  200 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 200 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 200 228 4 1 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 200 228 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 200 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 228 2 1 100 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 228 (accept_3_4 1 200 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 200 228))))))))))))))))))))))))))))) (allB_succ' 30 199 228 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 199 228 (accept_3_5 29 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 199 228 (Polychromatic418967fa.accept_16_12_7_4_1_687 28 199 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 199 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 228 (accept_3_5 26 199 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 228 (Polychromatic418967fa.accept_9_7_1_3_1_443
  25 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 228 (accept_3_5 23 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 228 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 199 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 228 (accept_3_5 20 199 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 199 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 228
  (Polychromatic418967fa.accept_22_18_1_8_1_12017 18 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 199 228 (accept_3_5 17 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 199 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 199 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 199 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 228 (accept_3_5 14 199 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 228 (Polychromatic418967fa.accept_7_6_3_4_1_294
  13 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 228
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 228 (accept_3_5 11 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 228 (Polychromatic418967fa.accept_13_10_4_7_1_2465 10 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 228 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 199 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 228 (accept_3_5 8 199 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 199 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 228
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 228 (accept_3_5 5 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 199 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 199 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 228 (accept_3_5 2 199 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 199 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 228)))))))))))))))))))))))))))))) (allB_succ' 31 198
  228 (Eq.refl Bool.true) (allA_succ_of_gcd 30 198 228 6 5 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 228 (Polychromatic418967fa.accept_16_13_6_4_1_3277 29 198
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 228 2 14 99 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 198 228 3 9 66 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 198 228 2 13 99 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 228
  (Polychromatic418967fa.accept_21_4_9_18_1_6001 25 198 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 228 6 4 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 198 228 (Polychromatic418967fa.accept_13_10_3_7_1_2517 23 198 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 228 2 11 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 198 228 3 7 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 228 2 10 99 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 198 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 228 6 3 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 198 228 (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 198 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 228 2 8 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 198 228 3 5 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 228 2 7 99 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 198 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 228 6 2 33 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 198 228 (Polychromatic418967fa.accept_13_11_3_7_1_2513 11 198 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 228 2 5 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 228 3 3 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 228 2 4 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 228 (Polychromatic418967fa.accept_21_7_9_18_1_7519
  7 198 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 228 6 1 33 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 198 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 228 2 2 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 198 228 3 1 66 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 198 228 2 1 99 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 198 228 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 198 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198 228))))))))))))))))))))))))))))))) (allB_succ' 32 197 228 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 197 228 (accept_3_4 31 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 197 228 (Polychromatic418967fa.accept_20_10_17_8_1_4856 30 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 228 (Polychromatic418967fa.accept_9_2_8_3_1_181
  29 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 228 (accept_3_4 28
  197 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 228
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 197 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 197 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 228 (accept_3_4 25 197 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 197 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 228 (Polychromatic418967fa.accept_9_5_8_3_1_437
  23 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 228 (accept_3_4 22
  197 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 228
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 197 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 197 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 228 (accept_3_4 19 197 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 197 228 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 197 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 228 (accept_3_4 16 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 228 (accept_3_4 13 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 197 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 228 (accept_3_4 10 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 228 (Polychromatic418967fa.accept_13_8_2_7_1_2452 8 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 228 (accept_3_4 7 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 197 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 228 (accept_3_4 4 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 197 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 228 (accept_3_4 1 197 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 228)))))))))))))))))))))))))))))))) (allB_succ' 33 196 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 196 228 4 8 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 196 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 196 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 228 2 15 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 228 (accept_3_5 29 196 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 228 4 7 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 228 (Polychromatic418967fa.accept_18_9_16_12_1_1143 27 196
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 228 2 13 98 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 228
  (Polychromatic418967fa.accept_21_4_7_18_1_7561 25 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 196 228 4 6 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 196 228 (accept_3_5 23 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  196 228 2 11 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 196 228 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 196 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 228 4 5 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 19
  196 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 228 2 9 98 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 228 (accept_3_5 17
  196 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 228 4 4 49 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 196 228 2 7 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 196 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 196 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 196 228 4 3 49 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 196 228 (accept_3_5 11 196 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 196 228 2 5 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 196 228 (Polychromatic418967fa.accept_18_9_16_12_1_1143
  9 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 228 4 2 49 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 228
  (Polychromatic418967fa.accept_24_7_4_12_1_11894 7 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 228 2 3 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 228 (accept_3_5 5 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  228 4 1 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 228 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 196 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 228 2 1 98 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 196 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 228))))))))))))))))))))))))))))))))) (allB_succ' 34
  195 228 (Eq.refl Bool.true) (allA_succ_of_gcd 33 195 228 3 11 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 195 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 195 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 195 228 3 10 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 195 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 195 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 228 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 228 3 9 65 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 195 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 195 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 195 228 3 8 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 195 228 3 7 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 195 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 195 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 195 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 228 3 6 65 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 195 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 228 3 5 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 195 228 3 4 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 195 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 195 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 195 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 228 3 3 65 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 228
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 195 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 228 3 2 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 195 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 195 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 228 3 1 65 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 195 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 195 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 228))))))))))))))))))))))))))))))))))
  (allB_succ' 35 194 228 (Eq.refl Bool.true) (allA_succ_of_gcd 34 194 228 2 17 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 228
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 228 2 16 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 228 (accept_3_4 31 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 228 2 15 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 194 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 228 2 14 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 228 2 13 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 228 (accept_3_4 25 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 228 2 12 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 194 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 228 2 11 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 228
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 228 2 10 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 228 (accept_3_4 19 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 228 2 9 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 194 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 228 2 8 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 228 2 7 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 228 (accept_3_4 13 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 228 2 6 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 194 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 228 2 5 97 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 228 2 4 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 228 (accept_3_4 7 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  228 2 3 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 228 (Polychromatic418967fa.accept_13_5_12_7_1_1080 5 194 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 228 2 2 97 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 228 (Polychromatic418967fa.accept_18_3_14_12_1_1141 3 194 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 228 2 1 97 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 228 (accept_3_4 1 194 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 228))))))))))))))))))))))))))))))))))) (allB_succ' 36 193 228
  (Eq.refl Bool.true) (allA_succ_of_accept 35 193 228 (accept_3_5 35 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 193 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 193 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 193 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 228 (accept_3_5 32 193 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 228 (Polychromatic418967fa.accept_10_1_3_8_1_136
  31 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 228
  (Polychromatic418967fa.accept_13_4_11_7_1_558 30 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 228 (accept_3_5 29 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 228 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 193 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 228 (accept_3_5 26 193 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 193 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 228 (accept_3_5 23 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 228 (Polychromatic418967fa.accept_13_9_11_7_1_1077 22 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 193 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 228 (accept_3_5 20 193 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 193 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 228
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 228 (accept_3_5 17 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 193 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 228 (accept_3_5 14 193 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 193 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 228
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 193 228 (accept_3_5 11 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 193 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 193 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 228 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 193
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 228 (accept_3_5 8 193 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 7
  193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 228 (accept_3_5 5 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 228 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 193 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 228 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 193 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 228 (accept_3_5 2 193 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 193 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 228)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 192 228 (Eq.refl Bool.true) (allA_succ_of_gcd 36 192 228 12 3 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 228 (Polychromatic418967fa.accept_10_5_2_8_1_135
  35 192 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 228 2 17 96 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 192 228 3 11 64
  76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 192 228 4 8 48
  57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 228
  (Polychromatic418967fa.accept_21_10_3_18_1_13594 31 192 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 192 228 6 5 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 192 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 192 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 228 4 7 48 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 192 228 3 9 64 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 192 228 2 13 96 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 228
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 192 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 228 12 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 228 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 192 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 228 2 11 96 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 192 228 3 7 64 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 192 228 4 5 48 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 228
  (Polychromatic418967fa.accept_21_19_3_18_1_7510 19 192 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 192 228 6 3 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 192 228 (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 192 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 228 4 4 48 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 192 228 3 5 64 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 192 228 2 7 96 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 228
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 228 12 1 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 228 (Polychromatic418967fa.accept_17_11_5_7_1_6177 11 192 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 228 2 5 96 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 192 228 3 3 64 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 192 228 4 2 48 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 228
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 192 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 228 6 1 32 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 192 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 228 4 1 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 228 3 1 64 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 228 2 1 96 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 228)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 191 228 (Eq.refl Bool.true) (allA_succ_of_accept 37 191 228 (accept_3_4 37 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 228 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 191 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 228 (accept_3_4 34 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 228 (accept_3_4 31 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 228 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 191 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 228
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 228 (accept_3_4 28 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 228 (accept_3_4 25 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 191 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 228 (accept_3_4 22 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 228 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 228 (accept_3_4 19 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 228 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 191 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 228 (accept_3_4 16 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 228 (accept_3_4 13 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 191 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 228 (accept_3_4 10 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 228 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 228 (accept_3_4 7 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 191 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 228 (accept_3_4 4 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 191 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 228 (Polychromatic418967fa.accept_13_2_9_7_1_164 2 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 228 (accept_3_4 1 191 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 228)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 190 228 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 190 228 38 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 190 228 (Polychromatic418967fa.accept_15_7_10_3_1_2891 37 190 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 190 228 2 18 95 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 190 228 (accept_3_5 35 190 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 190 228 2 17 95 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 190 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 190 228 2 16 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 190 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 190 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 190 228 2 15 95 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 228 (accept_3_5 29 190 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 190 228 2 14 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 190 228 (Polychromatic418967fa.accept_11_5_3_8_1_454
  27 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 228 2 13 95 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 228
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 228 2 12 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 228 (accept_3_5 23 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 228 2 11 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 228 (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 190 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 228 2 10 95 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 19 190 228 19 1 10 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 18 190 228 2 9 95 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 190 228
  (accept_3_5 17 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 190 228 2 8 95 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 190 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 190 228 2 7 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 190 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 190 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 190 228 2 6 95 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 190 228 (accept_3_5 11 190 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 190 228 2 5 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 190 228 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9
  190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 228 2 4 95 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 228
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 228 2 3 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 228 (accept_3_5 5 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  228 2 2 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 190 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 228 2 1 95 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 228 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 190 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 228)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 189 228 (Eq.refl Bool.true) (allA_succ_of_gcd 39 189 228 3 13 63 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 189 228
  (Polychromatic418967fa.accept_11_5_2_8_1_866 38 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 228 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 189 228 3 12 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 189 228 (Polychromatic418967fa.accept_15_5_9_3_1_528
  35 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 228
  (Polychromatic418967fa.accept_10_4_9_8_1_125 34 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 189 228 3 11 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 189 228 (Polychromatic418967fa.accept_17_15_2_7_1_7389 32 189 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 228
  (Polychromatic418967fa.accept_10_1_9_8_1_123 31 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 189 228 3 10 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 189 228 (Polychromatic418967fa.accept_17_12_2_7_1_3813 29 189 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 228
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 189 228 3 9 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 189 228 (Polychromatic418967fa.accept_17_9_2_7_1_2689 26 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 189 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 189 228 3 8 63 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 189 228
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 228 (Polychromatic418967fa.accept_16_6_13_4_1_643 22 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 189 228 3 7 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 228 (Polychromatic418967fa.accept_15_5_9_3_1_528
  20 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 228
  (Polychromatic418967fa.accept_20_19_9_8_1_12192 19 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 189 228 3 6 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 189 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 189 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 228
  (Polychromatic418967fa.accept_11_5_2_8_1_866 16 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 189 228 3 5 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 189 228 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 228 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 189
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 189 228 3 4 63 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 189 228
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 228 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 228 3 3 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 228 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 189 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 228
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 189 228 3 2 63 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 189 228 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 228 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 189 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 228 3 1 63 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 228
  (Polychromatic418967fa.accept_22_2_13_8_1_13622 2 189 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 189 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 228)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 188 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 188 228 4 10 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 228 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 188 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 188 228 2 19 94 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 188 228 (accept_3_4 37
  188 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 188 228 4 9 47 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 188 228
  (Polychromatic418967fa.accept_13_9_6_7_1_551 35 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 188 228 2 17 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 188 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 188 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 228 4 8 47 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 228 (accept_3_4 31 188 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 228 2 15 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 29
  188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 228 4 7 47 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 228
  (Polychromatic418967fa.accept_13_1_6_7_1_550 27 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 228 2 13 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 228 (accept_3_4 25 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 228 4 6 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 188 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 188 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 228 2 11 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 228 (Polychromatic418967fa.accept_16_5_12_4_1_4325
  21 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 228 4 5 47 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 228
  (accept_3_4 19 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 228 2 9 94 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 188 228 4 4 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 188 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 188 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 228 2 7 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 228 (accept_3_4 13 188 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 228 4 3 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 188 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 228 2 5 94 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 228 4 2 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 228 (accept_3_4 7 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  228 2 3 94 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 188 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 228 4 1 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 188 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 188 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 228 2 1 94 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 228 (accept_3_4 1 188 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 188 228))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 187 228
  (Eq.refl Bool.true) (allA_succ_of_accept 41 187 228 (accept_3_5 41 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 187 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 187 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 187 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 228 (accept_3_5 38 187 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 228 (Polychromatic418967fa.accept_7_2_5_4_1_115
  37 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 228 (accept_3_5 35 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 187 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 187 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 228 (accept_3_5 32 187 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 228 (accept_3_5 29 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 187 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 228 (accept_3_5 26 187 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 228 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 228 (accept_3_5 23 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 228 (Polychromatic418967fa.accept_18_3_7_12_1_1196 21 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 228 (accept_3_5 20 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 187 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 228
  (Polychromatic418967fa.accept_23_18_3_21_1_11949 18 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 187 228 (accept_3_5 17 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 187 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 187 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 187 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 228 (accept_3_5 14 187 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 228 (Polychromatic418967fa.accept_7_6_5_4_1_297
  13 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 228
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 228 (accept_3_5 11 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 187 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 228 (accept_3_5 8 187 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 228 (accept_3_5 5 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 187 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 228 (Polychromatic418967fa.accept_18_3_7_12_1_1196 3 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 228 (accept_3_5 2 187 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 187 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  228)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 186 228 (Eq.refl Bool.true) (allA_succ_of_gcd 42 186 228
  6 7 31 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 186
  228 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 186 228 2 20 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 186 228 3 13 62 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 186 228 2 19 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 186 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 186 228 6 6 31 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 186 228
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 228 2 17 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 186 228 3 11 62 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 186 228 2 16 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 186 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 186 228 6 5 31 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 186 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 228 2 14 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 186 228 3 9 62 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 186 228 2 13 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 186 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 186 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 186 228 6 4 31 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 186 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 228 2 11 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 186 228 3 7 62 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 186 228 2 10 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 186 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 186 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 186 228 6 3 31 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 186 228
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 228 2 8 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 186 228 3 5 62 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 186 228 2 7 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 186 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 186 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 186 228 6 2 31 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 186 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 228 2 5 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 186 228 3 3 62 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 186 228 2 4 93 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 186 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 186 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 228 6 1 31 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 5
  186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186 228 2 2 93 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 186 228 3 1 62 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 186 228 2 1 93 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 186 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 186 228))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 185 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 185 228 (accept_3_4 43 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 228 (accept_3_4 40 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 228 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 228 (accept_3_4 37 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 228 (accept_3_4 34 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 228
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 228 (accept_3_4 31 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 228 (Polychromatic418967fa.accept_13_4_3_7_1_2515 30 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 228 (accept_3_4 28 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 228
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 228 (accept_3_4 25 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 228 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 228 (accept_3_4 22 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 185 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 228
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 228 (accept_3_4 19 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 228 (Polychromatic418967fa.accept_22_18_9_8_1_1365 18 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 228 (accept_3_4 16 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 228
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 228 (accept_3_4 13 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 228 (accept_3_4 10 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 228 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 228 (accept_3_4 7 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 228 (accept_3_4 4 185 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 228 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 185 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 228 (accept_3_4 1 185 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  228)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 184 228 (Eq.refl Bool.true) (allA_succ_of_gcd 44 184
  228 4 11 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  184 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 184 228 2 21 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 184 228 (accept_3_5 41 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 184 228 4 10 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 184 228 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 184 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 228 2 19 92 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 228
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 184 228 4 9 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 184 228 (accept_3_5 35 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  184 228 2 17 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 184 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 184 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 228 4 8 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 228 (Polychromatic418967fa.accept_13_5_2_7_1_2414
  31 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 184 228 2 15 92 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 228
  (accept_3_5 29 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 184 228 4 7 46 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 184 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 184 228 2 13 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 184 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 184 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 228 4 6 46 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 184 228 (accept_3_5 23 184 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 184 228 2 11 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 228 (Polychromatic418967fa.accept_13_8_2_7_1_2452
  21 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 228 4 5 46 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 228 2 9 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 228 (accept_3_5 17 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 228 4 4 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 184 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 184 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 228 2 7 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 228 4 3 46 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 228 (accept_3_5 11
  184 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 228 2 5 92 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 228
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 184 228 4 2 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 184 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 184 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 228 2 3 92 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 228 (accept_3_5 5 184 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 228 4 1 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 184 228 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 184 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 228 2 1 92 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 228
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 184 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184 228))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 183 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 183 228 3 15 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 183 228 (Polychromatic418967fa.accept_16_12_7_4_1_687 44 183 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 183 228 3 14 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 183 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 183 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 228 (Polychromatic418967fa.accept_7_5_1_4_1_122
  40 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 183 228 3 13 61 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 183 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 228 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 183 228 3 12 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 183 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 35
  183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 228
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 34 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 183 228 3 11 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 183 228 (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 183 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 183 228 3 10 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 183 228 (Polychromatic418967fa.accept_13_3_1_7_1_1706 29 183 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 228
  (Polychromatic418967fa.accept_16_12_7_4_1_687 28 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 183 228 3 9 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 183 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 228 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 183
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 183 228 3 8 61 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 183 228
  (Polychromatic418967fa.accept_17_6_13_7_1_272 23 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 228 (Polychromatic418967fa.accept_21_1_15_18_1_7646 22 183 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 228 3 7 61 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 228
  (Polychromatic418967fa.accept_18_2_3_12_1_1155 20 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 228 3 6 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 17
  183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 228
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 183 228 3 5 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 183 228 (Polychromatic418967fa.accept_16_14_7_4_1_3243 14 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 228 (Polychromatic418967fa.accept_16_13_7_4_1_3248 13 183
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 228 3 4 61 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 228 3 3 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 228 (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 183 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 228
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 7 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 228 3 2 61 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 228 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 183 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 228 3 1 61 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 228
  (Polychromatic418967fa.accept_17_2_13_7_1_5011 2 183 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 183 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 228)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 182 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 182 228 2 23 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 182 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 182 228 2 22 91 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 182 228 (accept_3_4 43
  182 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 182 228 2 21 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 182 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 182 228 2 20 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 182 228 (Polychromatic418967fa.accept_17_5_12_7_1_2651 39 182 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 182 228 2 19 91 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 182 228 (accept_3_4 37 182 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 182 228 2 18 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 182 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 182 228 2 17 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 182 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 182 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 182 228 2 16 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 182 228 (accept_3_4 31 182 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 182 228 2 15 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 228 (Polychromatic418967fa.accept_15_14_2_3_1_1980
  29 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 228 2 14 91 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 228
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 228 2 13 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 228 (accept_3_4 25 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 228 2 12 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 182 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 228 2 11 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 228
  (Polychromatic418967fa.accept_16_5_6_4_1_3211 21 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 228 2 10 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 228 (accept_3_4 19 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 228 2 9 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 182 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 228 2 8 91 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 228
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 228 2 7 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 228 (accept_3_4 13 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 228 2 6 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 228 (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 182 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 228 2 5 91 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 228
  (Polychromatic418967fa.accept_21_9_14_18_1_7576 9 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 228 2 4 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 228 (accept_3_4 7 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  228 2 3 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 182 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 228 2 2 91 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 228 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 182 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 228 2 1 91 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 228 (accept_3_4 1 182 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 228))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  48 181 228 (Eq.refl Bool.true) (allA_succ_of_accept 47 181 228 (accept_3_5 47 181 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 181 228 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 181 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 181 228 (accept_3_5 44 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 181 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 181 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 228 (accept_3_5 41 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 181 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 228
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 181 228 (accept_3_5 38 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 181 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 181 228 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 228 (accept_3_5 35 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 181 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 228 (accept_3_5 32 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 228 (accept_3_5 29 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 228 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 181 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 228
  (Polychromatic418967fa.accept_20_7_1_8_1_10806 27 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 228 (accept_3_5 26 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 228 (accept_3_5 23 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 228
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 228 (accept_3_5 20 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 228 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 228 (accept_3_5 17 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 181 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 228 (accept_3_5 14 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 228 (accept_3_5 11 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 228 (accept_3_5 8 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 228 (accept_3_5 5 181 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 181 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 228 (accept_3_5 2 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 228)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 180 228 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 180 228 12 4 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 180 228 (Polychromatic418967fa.accept_21_5_12_18_1_7637 47 180 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 228 2 23 90 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 180 228 3 15 60 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 180 228 4 11 45
  57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 180 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 228 6 7 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 180 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 180 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 228 4 10 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 180 228 3 13 60 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 180 228 2 19 90 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 228 12 3 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 228 (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 180 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 228 2 17 90 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 180 228 3 11 60 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 180 228 4 8 45 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 228
  (Polychromatic418967fa.accept_13_5_11_7_1_559 31 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 228 6 5 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 180 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 180 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 228 4 7 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 228 3 9 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 228 2 13 90 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 228
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 180 228 12 2 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 180 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 228 2 11 90 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 228 3 7 60 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 228 4 5 45 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 228
  (Polychromatic418967fa.accept_21_19_12_18_1_1798 19 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 228 6 3 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 228 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 180 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 228 4 4 45 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 228 3 5 60 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 228 2 7 90 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 228 12 1 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 228 (Polychromatic418967fa.accept_21_11_12_18_1_4455 11 180 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 228 2 5 90 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 228 3 3 60 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 228 4 2 45 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 228
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 180 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 228 6 1 30 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 228 (Polychromatic418967fa.accept_13_5_11_7_1_559 5 180 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 228 4 1 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 228 3 1 60 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 228 2 1 90 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 180 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  228))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 179 228 (Eq.refl Bool.true) (allA_succ_of_accept
  49 179 228 (accept_3_4 49 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 228
  (Polychromatic418967fa.accept_21_6_11_18_1_10664 48 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 228 (accept_3_4 46 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 228 (Polychromatic418967fa.accept_18_9_17_12_1_462 45 179 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 228
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 228 (accept_3_4 43 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 228 (accept_3_4 40 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 228 (accept_3_4 37 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 228 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 228 (Polychromatic418967fa.accept_14_7_11_4_1_3455 35 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 228 (accept_3_4 34 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 179 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 228 (accept_3_4 31 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 228 (Polychromatic418967fa.accept_13_4_10_7_1_1701 30 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 228 (accept_3_4 28 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 228 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 228
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 179 228 (accept_3_4 25 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 179 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 179 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 179 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 228 (accept_3_4 22 179 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 228 (Polychromatic418967fa.accept_10_1_9_8_1_123
  21 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 228 (accept_3_4 19 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 228 (Polychromatic418967fa.accept_24_18_11_12_1_10310 18 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 228 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 228 (accept_3_4 16 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 179 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 228 (accept_3_4 13 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 228 (Polychromatic418967fa.accept_13_12_10_7_1_2433 12 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 228 (accept_3_4 10 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 228 (Polychromatic418967fa.accept_18_9_17_12_1_462 9 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 228
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 228 (accept_3_4 7 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 228 (accept_3_4 4 179 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 228 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 179 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 228 (accept_3_4 1 179 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  228)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 178 228 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  178 228 2 25 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 178 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 178 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 178 228 2 24 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 178 228 (accept_3_5 47 178 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 178 228 2 23 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 178 228 (Polychromatic418967fa.accept_13_6_9_7_1_2430 45 178
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 178 228 2 22 89 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 178 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 178 228 2 21 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 178 228 (accept_3_5 41 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 178 228 2 20 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 178 228 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 178 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 178 228 2 19 89 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 178 228
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 178 228 2 18 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 178 228 (accept_3_5 35 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 178 228 2 17 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 178 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 178 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 228 2 16 89 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 228
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 228 2 15 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 228 (accept_3_5 29 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 228 2 14 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 178 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 228 2 13 89 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 228
  (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 178 228 2 12 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 178 228 (accept_3_5 23 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 228 2 11 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 228 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 178 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 228 2 10 89 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 228
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 228 2 9 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 228 (accept_3_5 17 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 228 2 8 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 178 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 228 2 7 89 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 228
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 228 2 6 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 228 (accept_3_5 11 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 228 2 5 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 228 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 178 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 228 2 4 89 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 228
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 228 2 3 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 228 (accept_3_5 5 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  228 2 2 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 228 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 178 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 228 2 1 89 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 178 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178
  228))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 177 228 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  177 228 3 17 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 177 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 177 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 177 228 3 16 59 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 177 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 177 228 3 15 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 177 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 177 228 3 14 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 177 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 177 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 228 (Polychromatic418967fa.accept_7_5_2_4_1_126
  40 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 177 228 3 13 59 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 177 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 177 228 3 12 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 177 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 177 228 3 11 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 177 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 177 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 228 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 177 228 3 10 59 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 177 228
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 228 3 9 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 26
  177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 177 228 3 8 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 177 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 177 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 228 3 7 59 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 228 3 6 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 177 228 3 5 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 177 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 177 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 228 3 4 59 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 228 3 3 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 177 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 177 228 3 2 59 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 177 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 177 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 228 3 1 59 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 177 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 177 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 228)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  176 228 (Eq.refl Bool.true) (allA_succ_of_gcd 52 176 228 4 13 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 176 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 176 228 2 25 88 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 176 228 (accept_3_4 49
  176 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 176 228 4 12 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 176 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 176 228 2 23 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 176 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 176 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 176 228 4 11 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 176 228 (accept_3_4 43 176 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 176 228 2 21 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 176 228
  (Polychromatic418967fa.accept_23_18_15_21_1_13653 41 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 176 228 4 10 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 176 228 (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 176 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 176 228 2 19 88 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 176 228 (accept_3_4 37 176 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 176 228 4 9 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 176 228
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 176 228 2 17 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 176 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 176 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 228 4 8 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 228 (accept_3_4 31 176 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 228 2 15 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 29
  176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 228 4 7 44 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 228
  (Polychromatic418967fa.accept_23_4_15_21_1_13646 27 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 176 228 2 13 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 176 228 (accept_3_4 25 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 228 4 6 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 176 228 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 176 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 228 2 11 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 228 (Polychromatic418967fa.accept_15_6_11_3_1_1172
  21 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 228 4 5 44 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 228
  (accept_3_4 19 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 228 2 9 88 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 176 228 4 4 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 176 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 228 2 7 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 228 (accept_3_4 13 176 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 228 4 3 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 176 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 228 2 5 88 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 228
  (Polychromatic418967fa.accept_21_9_8_18_1_7516 9 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 228 4 2 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 228 (accept_3_4 7 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  228 2 3 88 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 176 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 228 4 1 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 176 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 176 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 228 2 1 88 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 228 (accept_3_4 1 176 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 176 228))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54
  175 228 (Eq.refl Bool.true) (allA_succ_of_accept 53 175 228 (accept_3_5 53 175 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 175 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 175 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 175 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 51
  175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 175 228 (accept_3_5 50
  175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 175 228
  (Polychromatic418967fa.accept_17_15_5_7_1_2694 49 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 175 228 (Polychromatic418967fa.accept_13_9_6_7_1_551 48 175 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 228 (accept_3_5 47 175 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 175 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 175 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 175 228 (Polychromatic418967fa.accept_14_3_7_4_1_118
  45 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 228 (accept_3_5 44
  175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 175 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 175 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 175 228 (accept_3_5 41 175 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 175 228 (Polychromatic418967fa.accept_13_1_6_7_1_550 40 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 228
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 228 (accept_3_5 38 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 228 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 228 (accept_3_5 35 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 175 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 175 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 228 (accept_3_5 32 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 228 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 228 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 228 (accept_3_5 29 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 175 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 228 (accept_3_5 26 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 175 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 228 (accept_3_5 23 175 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 228
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 228 (accept_3_5 20 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 228 (Polychromatic418967fa.accept_24_18_7_12_1_10188 18 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 228 (accept_3_5 17 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 175 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 228 (accept_3_5 14 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 228 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 228 (accept_3_5 11 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 175 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 228
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 228 (accept_3_5 8 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 175 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 228 (accept_3_5 5 175 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 228 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 175 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 228 (accept_3_5 2 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 175 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 228)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 174 228 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 174 228 6 9 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 228 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 174 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 228 2 26 87 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 174 228 3 17 58 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 174 228 2 25 87 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 174 228
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 228 6 8 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 174 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 228 2 23 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 174 228 3 15 58 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 228 2 22 87 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 228
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 228 6 7 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 174 228 (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 228 2 20 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 174 228 3 13 58 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 228 2 19 87 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 228 6 6 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 174 228 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 228 2 17 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 228 3 11 58 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 228 2 16 87 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 228 6 5 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 174 228 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 228 2 14 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 228 3 9 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 228 2 13 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 228
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 228 6 4 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 228 2 11 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 228 3 7 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 228 2 10 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 228 6 3 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 228 2 8 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 228 3 5 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 228 2 7 87 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 228
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 228 6 2 29 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 228 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 228 2 5 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 228 3 3 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 228 2 4 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 228 (Polychromatic418967fa.accept_16_7_14_4_1_1362
  7 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 228 6 1 29 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 174 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 174 228 2 2 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 174 228 3 1 58 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 174 228 2 1 87 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 174 228 (Polychromatic418967fa.accept_16_1_14_4_1_3220 1 174 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 228))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  56 173 228 (Eq.refl Bool.true) (allA_succ_of_accept 55 173 228 (accept_3_4 55 173 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 173 228 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 53 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 228 (accept_3_4 52 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 50 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 228 (accept_3_4 49 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 228
  (Polychromatic418967fa.accept_23_1_12_21_1_13652 47 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 173 228 (accept_3_4 46 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 173 228 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 173 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 173 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 228 (accept_3_4 43 173 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 228 (Polychromatic418967fa.accept_9_6_2_3_1_771
  42 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 228 (accept_3_4 40 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 228 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 228 (Polychromatic418967fa.accept_13_12_4_7_1_2520 38 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 228 (accept_3_4 37 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 173 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 228 (accept_3_4 34 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 228 (accept_3_4 31 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 228 (accept_3_4 28 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 228 (accept_3_4 25 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 228 (accept_3_4 22 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 228 (accept_3_4 19 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 228 (Polychromatic418967fa.accept_20_18_13_8_1_9398 18 173 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 228
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 228 (accept_3_4 16 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 228 (accept_3_4 13 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 228 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 173 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 228
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 228 (accept_3_4 10 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 228 (accept_3_4 7 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 173 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 228 (accept_3_4 4 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 228 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 173 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 228 (accept_3_4 1 173 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 172 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 172 228 4 14 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 172 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 55 172 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 172 228 2 27 86 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 172 228 (accept_3_5 53
  172 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 172 228 4 13 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 172 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 172 228 2 25 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 172 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 172 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 172 228 4 12 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 172 228 (accept_3_5 47 172 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 172 228 2 23 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 172 228 (Polychromatic418967fa.accept_10_5_2_8_1_135
  45 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 172 228 4 11 43 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 172 228
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 172 228 2 21 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 172 228 (accept_3_5 41 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 172 228 4 10 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 172 228 (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 172 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 228 2 19 86 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 228
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 228 4 9 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 172 228 (accept_3_5 35 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  172 228 2 17 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 172 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 172 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 228 4 8 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 31
  172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 228 2 15 86 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 228 (accept_3_5 29
  172 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 228 4 7 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 228
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 172 228 2 13 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 172 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 172 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 172 228 4 6 43 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 172 228 (accept_3_5 23 172 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 172 228 2 11 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 172 228 (Polychromatic418967fa.accept_13_8_3_7_1_2455
  21 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 228 4 5 43 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 228
  (Polychromatic418967fa.accept_15_4_7_3_1_119 19 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 228 2 9 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 228 (accept_3_5 17 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 228 4 4 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 172 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 172 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 228 2 7 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 228 4 3 43 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 228 (accept_3_5 11
  172 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 228 2 5 86 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 228
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 172 228 4 2 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 172 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 172 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 228 2 3 86 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 228 (accept_3_5 5 172 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 228 4 1 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 172 228 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 172 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 228 2 1 86 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 228
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 172 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172 228))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 171 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 171 228 57 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 171 228 (Polychromatic418967fa.accept_15_11_6_3_1_1192 56 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 171 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 171 228 3 18 57 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 171 228
  (Polychromatic418967fa.accept_10_3_1_8_1_132 53 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 228 (Polychromatic418967fa.accept_18_16_9_12_1_1182 52 171 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 171 228 3 17 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 171 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 171 228 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 171 228 3 16 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 171 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 47
  171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 228
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 46 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 171 228 3 15 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 171 228 (Polychromatic418967fa.accept_13_5_2_7_1_2414 44 171 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 171 228 3 14 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 171 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 171 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 228
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 40 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 171 228 3 13 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 171 228 19 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 171 228 (Polychromatic418967fa.accept_20_17_11_8_1_4894 37 171 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 228 3 12 57 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 228
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 228 3 11 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 228
  (Polychromatic418967fa.accept_21_11_3_18_1_3068 32 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 171 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 171 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 228 3 10 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 228 (Polychromatic418967fa.accept_16_12_11_4_1_1359 28 171 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 228 3 9 57 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 228
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 228 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 228 3 8 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 23
  171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 171 228 3 7 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 171 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 171 228 19 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 18 171 228 3 6 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 228
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 171 228 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 171 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 228 3 5 57 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 228
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 228 3 4 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 228 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  11 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 228
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 228 3 3 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 171 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 228 3 2 57 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 228
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 228 (Polychromatic418967fa.accept_18_4_9_12_1_1175 4 171 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 228 3 1 57 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 228 (Polychromatic418967fa.accept_21_2_3_18_1_5952 2 171 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 171 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 170 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 170 228 2 29 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 170 228 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 170 228 2 28 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 170 228 (accept_3_4 55 170 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 170 228 2 27 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 228 (Polychromatic418967fa.accept_15_8_5_3_1_1990
  53 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 228 2 26 85 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 228
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 228 2 25 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 228 (accept_3_4 49 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 228 2 24 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 228 2 23 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 228
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 228 2 22 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 228 (accept_3_4 43 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 228 2 21 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 228 2 20 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 228
  (Polychromatic418967fa.accept_15_9_5_3_1_554 39 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 228 2 19 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 228 (accept_3_4 37 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 228 2 18 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 228 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 228 2 17 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 228 2 16 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 228 (accept_3_4 31 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 228 2 15 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 228 2 14 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 228 2 13 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 228 (accept_3_4 25 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 228 2 12 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 228 2 11 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 228
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 228 2 10 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 228 (accept_3_4 19 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 228 2 9 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 228 (Polychromatic418967fa.accept_15_2_5_3_1_552 17 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 228 2 8 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 228
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 228 2 7 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 228 (accept_3_4 13 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 228 2 6 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 170 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 228 2 5 85 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 228
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 228 2 4 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 228 (accept_3_4 7 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  228 2 3 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 170 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 228 2 2 85 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 228 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 170 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 228 2 1 85 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 228 (accept_3_4 1 170 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 169 228 (Eq.refl Bool.true) (allA_succ_of_accept 59 169 228 (accept_3_5 59 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 169 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 169 228
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 169 228 (accept_3_5 56 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 169 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 169 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 228 (accept_3_5 53 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 169 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 228 (accept_3_5 50 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 228 (Polychromatic418967fa.accept_22_4_15_8_1_7222 48 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 228 (accept_3_5 47 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 169 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 228 (accept_3_5 44 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 228 (Polychromatic418967fa.accept_16_11_9_4_1_5438 43 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 228 (accept_3_5 41 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 228
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 39 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 228 (accept_3_5 38 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 228 (Polychromatic418967fa.accept_21_15_1_18_1_3066 36 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 228 (accept_3_5 35 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 228 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 169
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 228 (accept_3_5 32 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 228 (Polychromatic418967fa.accept_16_14_9_4_1_6693 30 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 228 (accept_3_5 29 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 169 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 228
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 228 (accept_3_5 26 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 228 (Polychromatic418967fa.accept_14_11_1_4_1_4445 25 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 228 (accept_3_5 23 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 228
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 228 (accept_3_5 20 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 228 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 228 (accept_3_5 17 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 228 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 169
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 228 (accept_3_5 14 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 228 (accept_3_5 11 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 228
  (Polychromatic418967fa.accept_21_9_1_18_1_1761 9 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 228 (accept_3_5 8 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 228 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 228 (accept_3_5 5 169 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 169 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 228 (accept_3_5 2 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 168 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 168 228 12 5 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 168 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 168 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 228 2 29 84 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 168 228 3 19 56 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 168 228 4 14 42
  57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 168 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 228 6 9 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 168 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 168 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 228 4 13 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 168 228 3 17 56 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 228 2 25 84 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 228 12 4 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 168 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 228 2 23 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 168 228 3 15 56 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 228 4 11 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 228 6 7 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 168 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 168 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 228 4 10 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 228 3 13 56 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 228 2 19 84 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 228 12 3 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 168 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 228 2 17 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 168 228 3 11 56 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 228 4 8 42 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 228 6 5 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 168 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 168 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 228 4 7 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 228 3 9 56 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 228 2 13 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 228 12 2 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 168 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 228 2 11 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 228 3 7 56 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 228 4 5 42 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 228 6 3 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 168 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 228 4 4 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 228 3 5 56 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 228 2 7 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 228
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 228 12 1 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 168 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 228 2 5 84 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 228 3 3 56 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 228 4 2 42 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 228
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 168 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 228 6 1 28 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 228 4 1 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 228 3 1 56 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 228 2 1 84 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 167 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 167 228 (accept_3_4 61 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 167 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 228 (accept_3_4 58 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 228 (Polychromatic418967fa.accept_13_5_11_7_1_559 57 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 228 (accept_3_4 55 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 228 (accept_3_4 52 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 228
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 228 (accept_3_4 49 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 228 (Polychromatic418967fa.accept_13_9_11_7_1_1077 48 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 228 (accept_3_4 46 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 228 (accept_3_4 43 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 228 (Polychromatic418967fa.accept_20_1_7_8_1_4877 41 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 228 (accept_3_4 40 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 228 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 167
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 228 (accept_3_4 37 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 228 (Polychromatic418967fa.accept_21_15_20_18_1_5985 36 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 228 (accept_3_4 34 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 167 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 228
  (Polychromatic418967fa.accept_21_11_20_18_1_7656 32 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 167 228 (accept_3_4 31 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 167 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 167 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 167 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 228 (accept_3_4 28 167 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 27
  167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 228 (accept_3_4 25 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 228 (accept_3_4 22 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 228 (Polychromatic418967fa.accept_17_4_14_7_1_4965 21 167 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 228 (accept_3_4 19 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 228 (Polychromatic418967fa.accept_13_5_11_7_1_559 18 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 228 (accept_3_4 16 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 228
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 228 (accept_3_4 13 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 228 (accept_3_4 10 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 228
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 228 (accept_3_4 7 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 228 (accept_3_4 4 167 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 167 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 228 (accept_3_4 1 167 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 166 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 166 228 2 31 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 166 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 166 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 166 228 2 30 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 166 228 (accept_3_5 59 166 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 166 228 2 29 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 166 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 57
  166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 166 228 2 28 83 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 166 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 166 228 2 27 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 228 (accept_3_5 53 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 228 2 26 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 166 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 228 2 25 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 228
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 49 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 228 2 24 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 228 (accept_3_5 47 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 228 2 23 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 228 (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 166 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 228 2 22 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 228 2 21 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 228 (accept_3_5 41 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 228 2 20 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 228 (Polychromatic418967fa.accept_23_16_5_21_1_13651 39 166 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 228 2 19 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 228 2 18 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 228 (accept_3_5 35 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 228 2 17 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 166 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 228 2 16 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 228
  (Polychromatic418967fa.accept_29_2_21_25_1_13650 31 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 166 228 2 15 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 166 228 (accept_3_5 29 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 228 2 14 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 166 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 228 2 13 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 228
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 228 2 12 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 228 (accept_3_5 23 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 228 2 11 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 228 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 166 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 228 2 10 83 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 228
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 228 2 9 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 228 (accept_3_5 17 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 228 2 8 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 166 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 228 2 7 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 228 2 6 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 228 (accept_3_5 11 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 228 2 5 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 166 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 228 2 4 83 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 228
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 228 2 3 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 228 (accept_3_5 5 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  228 2 2 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 228 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 166 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 228 2 1 83 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 166 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 165 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 165 228 3 21 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 165 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 165 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 228
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 61 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 165 228 3 20 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 165 228 (Polychromatic418967fa.accept_24_11_21_12_1_13649 59 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 228
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 58 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 165 228 3 19 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 165 228 (Polychromatic418967fa.accept_13_4_9_7_1_2402 56 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 228
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 165 228 3 18 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 165 228 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 228
  (Polychromatic418967fa.accept_10_2_5_8_1_139 52 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 165 228 3 17 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 165 228 (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 228
  (Polychromatic418967fa.accept_8_1_5_4_1_388 49 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 165 228 3 16 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 165 228 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 228
  (Polychromatic418967fa.accept_22_2_11_8_1_13586 46 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 165 228 3 15 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 165 228 (Polychromatic418967fa.accept_16_12_5_4_1_3275 44 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 228
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 165 228 3 14 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 165 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 165 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 228 (Polychromatic418967fa.accept_16_8_5_4_1_674
  40 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 228 3 13 55 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 228
  (Polychromatic418967fa.accept_16_6_5_4_1_4330 38 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 228 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 228 3 12 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 228 (Polychromatic418967fa.accept_14_7_11_4_1_3455
  35 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 228
  (Polychromatic418967fa.accept_13_8_9_7_1_530 34 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 165 228 3 11 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 165 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 165 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 228
  (Polychromatic418967fa.accept_16_15_5_4_1_6678 31 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 165 228 3 10 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 165 228 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 228
  (Polychromatic418967fa.accept_13_2_9_7_1_164 28 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 165 228 3 9 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 165 228 (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 165 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 228 3 8 55 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 228
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 228 3 7 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 228 (Polychromatic418967fa.accept_17_3_12_7_1_4949
  20 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 228
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 165 228 3 6 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 228 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 165
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 228 3 5 55 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 228
  (Polychromatic418967fa.accept_18_14_3_12_1_3249 14 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 165 228 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 165 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 228 3 4 55 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 228
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 228 (Polychromatic418967fa.accept_20_10_5_8_1_6385 10 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 228 3 3 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 228 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 165 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 228
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 165 228 3 2 55 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 165 228 (Polychromatic418967fa.accept_17_5_12_7_1_2651 5 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 228 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 165 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 228 3 1 55 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 228
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 165 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 165 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165 228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 164 228 (Eq.refl Bool.true) (allA_succ_of_gcd 64 164 228 4 16 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 228
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 228 2 31 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 228 (accept_3_4 61 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 228 4 15 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 164 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 228 2 29 82 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 228 4 14 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 228 (accept_3_4 55 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 228 2 27 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 164 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 228 4 13 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 228
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 228 2 25 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 228 (accept_3_4 49 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 228 4 12 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 228 (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 164 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 228 2 23 82 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 228
  (Polychromatic418967fa.accept_21_3_17_18_1_13598 45 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 164 228 4 11 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 164 228 (accept_3_4 43 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 228 2 21 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 164 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 228 4 10 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 228
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 228 2 19 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 228 (accept_3_4 37 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 228 4 9 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 164 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 228 2 17 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 33
  164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 228 4 8 41 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 228 (accept_3_4 31
  164 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 228 2 15 82 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 228 4 7 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 164 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 228 2 13 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 228 (accept_3_4 25 164 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 228 4 6 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 164 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 228 2 11 82 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 228
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 228 4 5 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 228 (accept_3_4 19 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 228 2 9 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 164 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 228 4 4 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 228 2 7 82 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 228 (accept_3_4 13
  164 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 228 4 3 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 228
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 164 228 2 5 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 164 228 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 164 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 228 4 2 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 228 (accept_3_4 7 164 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 228 2 3 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 5
  164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 228 4 1 41 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 228
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 228 2 1 82 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 228 (accept_3_4 1 164 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 163 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 163 228 (accept_3_5 65 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 163 228 (Polychromatic418967fa.accept_24_16_19_12_1_8458 64 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 163 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 163 228 (accept_3_5 62 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 163 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 163 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 163 228 (accept_3_5 59 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 163 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 163 228 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 228 (accept_3_5 56 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 163 228 (accept_3_5 53 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 163 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 163 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 228 (accept_3_5 50 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 163 228 (accept_3_5 47 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 163 228 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 163 228 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 228 (accept_3_5 44 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 228 (accept_3_5 41 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 228 (accept_3_5 38 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 228 (Polychromatic418967fa.accept_17_3_10_7_1_2646 37 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 228
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 228 (accept_3_5 35 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 228 (accept_3_5 32 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 228
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 228 (accept_3_5 29 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 228 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 228 (accept_3_5 26 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 228 (accept_3_5 23 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 228 (accept_3_5 20 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 228
  (Polychromatic418967fa.accept_17_1_10_7_1_12461 18 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 163 228 (accept_3_5 17 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 163 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 163 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 228 (accept_3_5 14 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 228 (Polychromatic418967fa.accept_7_6_2_4_1_291
  13 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 228 (accept_3_5 11 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 228 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 228 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 228 (accept_3_5 8 163 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 228 (accept_3_5 5 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 163 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 228 (Polychromatic418967fa.accept_17_3_10_7_1_2646 3 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 228 (accept_3_5 2 163 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 163 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 162 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 162 228 6 11 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 162 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 228 2 32 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 162 228 3 21 54 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 162 228 2 31 81 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 162 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 228 6 10 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 162 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 228 2 29 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 162 228 3 19 54 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 228 2 28 81 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 228
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 228 6 9 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 162 228 (Polychromatic418967fa.accept_13_1_6_7_1_550 53 162 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 228 2 26 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 162 228 3 17 54 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 162 228 2 25 81 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 228
  (Polychromatic418967fa.accept_17_15_9_7_1_3816 49 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 228 6 8 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 162 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 162 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 228 2 23 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 162 228 3 15 54 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 228 2 22 81 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 228
  (Polychromatic418967fa.accept_13_4_6_7_1_2471 43 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 228 6 7 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 162 228 (Polychromatic418967fa.accept_21_20_15_18_1_4457 41 162 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 228 2 20 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 162 228 3 13 54 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 162 228 2 19 81 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 228
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 228 6 6 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 162 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 228 2 17 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 228 3 11 54 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 228 2 16 81 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 228 6 5 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 162 228 (Polychromatic418967fa.accept_21_8_15_18_1_13648 29 162 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 228 2 14 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 228 3 9 54 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 228 2 13 81 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 228
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 228 6 4 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 228 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 162 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 228 2 11 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 228 3 7 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 228 2 10 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 228 6 3 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 162 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 228 2 8 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 228 3 5 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 228 2 7 81 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 228
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 228 6 2 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 228 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 162 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 228 2 5 81 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 228 3 3 54 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 228 2 4 81 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 228
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 228 6 1 27 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 162 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 228 2 2 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 228 3 1 54 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 228 2 1 81 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 228 (Polychromatic418967fa.accept_13_1_6_7_1_550 1
  162 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 161 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 161 228 (accept_3_4 67 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 228 (Polychromatic418967fa.accept_14_10_7_4_1_3453 66 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 228 (accept_3_4 64 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 228 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 228
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 62 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 228 (accept_3_4 61 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 228 (accept_3_4 58 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 228 (Polychromatic418967fa.accept_21_15_14_18_1_7645 57 161 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 228 (accept_3_4 55 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 228 (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 228 (accept_3_4 52 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 228 (accept_3_4 49 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 228 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 228 (accept_3_4 46 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 228
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 44 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 161 228 (accept_3_4 43 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 161 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 161 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 228 (accept_3_4 40 161 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 228 (Polychromatic418967fa.accept_10_9_1_8_1_755
  39 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 228 (accept_3_4 37 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 228 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 228 (Polychromatic418967fa.accept_16_3_1_4_1_5426 35 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 228 (accept_3_4 34 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 161 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 228 (accept_3_4 31 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 228 (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 228 (accept_3_4 28 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 228 (Polychromatic418967fa.accept_18_9_17_12_1_462 27 161 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 228
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 228 (accept_3_4 25 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 228 (accept_3_4 22 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 228 (accept_3_4 19 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 228 (Polychromatic418967fa.accept_17_1_8_7_1_4982 18 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 228 (Polychromatic418967fa.accept_14_3_7_4_1_118 17 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 228 (accept_3_4 16 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 161 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 228 (accept_3_4 13 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 228 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 228 (accept_3_4 10 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 228 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 228
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 228 (accept_3_4 7 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 228 (accept_3_4 4 161 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 228 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 161 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 228
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 228 (accept_3_4 1 161 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 160 228 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 160 228 4 17 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 160 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 160 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 160 228 2 33 80 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 160 228 (accept_3_5 65 160 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 160 228 4 16 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 160 228 (Polychromatic418967fa.accept_13_11_4_7_1_2419
  63 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 160 228 2 31 80 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 160 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 160 228 4 15 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 160 228 (accept_3_5 59 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 160 228 2 29 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 160 228 (Polychromatic418967fa.accept_21_15_13_18_1_7523 57 160 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 160 228 4 14 40 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 160 228
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 160 228 2 27 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 160 228 (accept_3_5 53 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 160 228 4 13 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 160 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 160 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 228 2 25 80 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 228
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 160 228 4 12 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 160 228 (accept_3_5 47 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 228 2 23 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 160 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 160 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 160 228 4 11 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 160 228
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 160 228 2 21 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 160 228 (accept_3_5 41 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 160 228 4 10 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 160 228 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 160 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 160 228 2 19 80 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 228 4 9 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 160 228 (accept_3_5 35 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  160 228 2 17 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 160 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 160 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 228 4 8 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 228 2 15 80 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 228 (accept_3_5 29
  160 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 228 4 7 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 228
  (Polychromatic418967fa.accept_18_9_16_12_1_1143 27 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 160 228 2 13 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 160 228 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 160 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 160 228 4 6 40 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 228 (accept_3_5 23 160 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 228 2 11 80 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 228
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 21 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 228 4 5 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 160 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 160 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 228 2 9 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 228 (accept_3_5 17 160 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 228 4 4 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 160 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 228 2 7 80 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 228
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 228 4 3 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 160 228 (accept_3_5 11 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 228 2 5 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 160 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 160 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 228 4 2 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 228 (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 160 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 228 2 3 80 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 228 (accept_3_5 5
  160 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 228 4 1 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 160 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 160 228 2 1 80 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 160 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 160 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 160 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 159 228 (Eq.refl Bool.true) (allA_succ_of_gcd 69 159 228 3 23 53 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 159 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 68 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 159 228 3 22 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 159 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 64 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 159 228 3 21 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 159 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 62 159 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 228 (Polychromatic418967fa.accept_9_7_6_3_1_456
  61 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 159 228 3 20 53 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 159 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 159 228 3 19 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 159 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 56
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 159 228 3 18 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 159 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 53 159 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 228 (Polychromatic418967fa.accept_9_7_6_3_1_456
  52 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 159 228 3 17 53 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 159 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 159 228 3 16 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 159 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 47
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 46 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 159 228 3 15 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 159 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 159 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 228 (Polychromatic418967fa.accept_7_1_5_4_1_134
  43 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 159 228 3 14 53 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 159 228
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 159 228 3 13 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 159 228 (Polychromatic418967fa.accept_9_2_6_3_1_178 38
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 159 228 3 12 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 159 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 159 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 228 (Polychromatic418967fa.accept_7_6_5_4_1_297
  34 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 228 3 11 53 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 228 3 10 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 159 228 3 9 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 159 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 26 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 159 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 228 3 8 53 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 228
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 228 3 7 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 159 228 3 6 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 159 228 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 159 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 228 3 5 53 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 228 3 4 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 11
  159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 228
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 159 228 3 3 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 159 228 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 228 3 2 53 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 159 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 228 3 1 53 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 159 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 159 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 158 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 158 228 2 35 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 158 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 158 228 2 34 79 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 158 228 (accept_3_4 67
  158 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 158 228 2 33 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 158 228
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 158 228 2 32 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 158 228 (Polychromatic418967fa.accept_16_15_14_4_1_6649 63 158 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 158 228 2 31 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 158 228 (accept_3_4 61 158 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 158 228 2 30 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 158 228
  (Polychromatic418967fa.accept_22_15_4_8_1_10600 59 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 158 228 2 29 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 158 228 (Polychromatic418967fa.accept_13_5_2_7_1_2414 57 158 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 158 228 2 28 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 158 228 (accept_3_4 55 158 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 158 228 2 27 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 158 228
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 158 228 2 26 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 158 228 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 158 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 158 228 2 25 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 158 228 (accept_3_4 49 158 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 158 228 2 24 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 158 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 47
  158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 228 2 23 79 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 228
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 228 2 22 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 228 (accept_3_4 43 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 228 2 21 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 228 (Polychromatic418967fa.accept_15_11_8_3_1_1943 41 158 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 228 2 20 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 228
  (Polychromatic418967fa.accept_15_9_8_3_1_557 39 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 228 2 19 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 228 (accept_3_4 37 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 228 2 18 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 158 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 228 2 17 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 228
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 228 2 16 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 228 (accept_3_4 31 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 228 2 15 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 158 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 228 2 14 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 228
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 228 2 13 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 228 (accept_3_4 25 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 228 2 12 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 228 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 158 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 228 2 11 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 228
  (Polychromatic418967fa.accept_13_8_2_7_1_2452 21 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 228 2 10 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 228 (accept_3_4 19 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 228 2 9 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 228 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 158 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 228 2 8 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 228
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 228 2 7 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 228 (accept_3_4 13 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 228 2 6 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 228 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 158 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 228 2 5 79 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 228
  (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 228 2 4 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 228 (accept_3_4 7 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  228 2 3 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 228 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 158 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 228 2 2 79 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 228 (Polychromatic418967fa.accept_18_3_14_12_1_1141 3 158 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 228 2 1 79 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 228 (accept_3_4 1 158 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 157 228 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 157 228 (accept_3_5 71 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 157 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 157 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 157 228 (accept_3_5 68 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 157 228 (Polychromatic418967fa.accept_20_7_17_8_1_3452 67 157 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 157 228
  (Polychromatic418967fa.accept_21_3_10_18_1_7631 66 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 157 228 (accept_3_5 65 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 157 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 157 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 228 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 157
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 228 (accept_3_5 62 157
  228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 157 228
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 157 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 157 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 228 (accept_3_5 59 157 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 157 228 (Polychromatic418967fa.accept_13_6_1_7_1_1690 58 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 228 (accept_3_5 56 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 228 (Polychromatic418967fa.accept_16_6_13_4_1_643 54 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 228 (accept_3_5 53 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 157 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 228
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 228 (accept_3_5 50 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 228 (accept_3_5 47 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 228
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 228 (accept_3_5 44 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 228 (accept_3_5 41 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 228 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 157 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 228
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 228 (accept_3_5 38 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 228 (accept_3_5 35 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 228
  (Polychromatic418967fa.accept_8_1_5_4_1_388 33 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 228 (accept_3_5 32 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 228 (Polychromatic418967fa.accept_17_14_4_7_1_7439 31 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 228 (Polychromatic418967fa.accept_20_10_17_8_1_4856 30 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 228 (accept_3_5 29 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 157 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 228
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 228 (accept_3_5 26 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 228 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 228 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 228 (accept_3_5 23 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 228
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 21 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 228 (accept_3_5 20 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 228 (Polychromatic418967fa.accept_24_18_13_12_1_6679 18 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 228 (accept_3_5 17 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 157 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 228 (accept_3_5 14 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 228 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 228 (accept_3_5 11 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 228 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 157 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 228
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 228 (accept_3_5 8 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 228 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 228 (accept_3_5 5 157 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 228 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 157 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 228
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 228 (accept_3_5 2 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73
  156 228 (Eq.refl Bool.true) (allA_succ_of_gcd 72 156 228 12 6 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 156 228 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 156 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 228 2 35 78 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 156 228 3 23 52 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 156 228 4 17 39
  57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 156 228
  (Polychromatic418967fa.accept_16_3_12_4_1_170 67 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 228 6 11 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 228 (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 156 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 228 4 16 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 156 228 3 21 52 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 156 228 2 31 78 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 228 12 5 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 228 (Polychromatic418967fa.accept_16_11_12_4_1_3195 59 156 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 228 2 29 78 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 156 228 3 19 52 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 228 4 14 39 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 228 6 9 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 156 228 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 156 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 228 4 13 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 156 228 3 17 52 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 228 2 25 78 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 228
  (Polychromatic418967fa.accept_11_5_2_8_1_866 49 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 228 12 4 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 156 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 228 2 23 78 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 156 228 3 15 52 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 156 228 4 11 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 228
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 228 6 7 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 156 228 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 156 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 228 4 10 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 228 3 13 52 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 228 2 19 78 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 228
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 228 12 3 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 228 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 156 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 228 2 17 78 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 228 3 11 52 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 228 4 8 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 228
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 228 6 5 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 156 228 (Polychromatic418967fa.accept_16_13_12_4_1_4323 29 156 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 228 4 7 39 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 228 3 9 52 76 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 228 2 13 78 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 228
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 228 12 2 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 228 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 156 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 228 2 11 78 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 228 3 7 52 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 228 4 5 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 228
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 228 6 3 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 228 (Polychromatic418967fa.accept_16_1_12_4_1_695 17 156 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 228 4 4 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 228 3 5 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 228 2 7 78 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 228
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 228 12 1 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 228 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 156 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 228 2 5 78 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 156 228 3 3 52 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 228 4 2 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 228
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 7 156 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 228 6 1 26 38 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 228 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 228 4 1 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 228 3 1 52 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 228 2 1 78 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 228 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 156 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 155 228 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 155 228 (accept_3_4 73 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 155 228 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 155 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 228 (accept_3_4 70 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 228 (Polychromatic418967fa.accept_9_6_2_3_1_771
  69 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 228 (accept_3_4 67 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 228 (Polychromatic418967fa.accept_20_5_15_8_1_4930 65 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 228 (accept_3_4 64 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 228 (accept_3_4 61 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 228 (accept_3_4 58 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 228 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 228
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 228 (accept_3_4 55 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 228 (accept_3_4 52 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 228 (accept_3_4 49 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 228 (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 228 (accept_3_4 46 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 228 (accept_3_4 43 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 228 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 228 (accept_3_4 40 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 228
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 228 (accept_3_4 37 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 228 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 228 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 228 (accept_3_4 34 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 228 (accept_3_4 31 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 228 (Polychromatic418967fa.accept_13_4_12_7_1_2439 30 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 228 (Polychromatic418967fa.accept_17_12_2_7_1_3813 29 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 228 (accept_3_4 28 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 228 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 155
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 228
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 228 (accept_3_4 25 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 228 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 228 (accept_3_4 22 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 228 (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 228
  (Polychromatic418967fa.accept_22_20_1_8_1_13628 20 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 155 228 (accept_3_4 19 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 155 228 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 155 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 228 (accept_3_4 16 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 228 (Polychromatic418967fa.accept_8_7_3_4_1_404
  15 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 228
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 228 (accept_3_4 13 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 228 (Polychromatic418967fa.accept_13_11_12_7_1_2443 11 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 228 (accept_3_4 10 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 228 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 155 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 228
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 228 (accept_3_4 7 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 228 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 228 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 228 (accept_3_4 4 155 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 228 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 155 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 228
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 228 (accept_3_4 1 155 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 154 228 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 154 228 2 37 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 154 228 (Polychromatic418967fa.accept_20_13_14_8_1_4850 73 154 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 154 228 2 36 77 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 154 228 (accept_3_5 71
  154 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 154 228 2 35 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 154 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 154 228 2 34 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 154 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 154 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 154 228 2 33 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 154 228 (accept_3_5 65 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 154 228 2 32 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 154 228
  (Polychromatic418967fa.accept_18_9_10_12_1_5793 63 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 154 228 2 31 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 154 228 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 154 228 2 30 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 154 228 (accept_3_5 59 154 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 154 228 2 29 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 154 228
  (Polychromatic418967fa.accept_13_5_11_7_1_559 57 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 154 228 2 28 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 154 228 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 154 228 2 27 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 228 (accept_3_5 53 154 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 228 2 26 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 228
  (Polychromatic418967fa.accept_9_6_1_3_1_191 51 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 154 228 2 25 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 154 228 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 154 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 154 228 2 24 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 228 (accept_3_5 47 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 154 228 2 23 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 154 228 (Polychromatic418967fa.accept_17_11_1_7_1_2657
  45 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 154 228 2 22 77 114
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 154 228
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 154 228 2 21 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 154 228 (accept_3_5 41 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 228 2 20 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 228 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 154 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 228 2 19 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 228
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 228 2 18 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 228 (accept_3_5 35 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 228 2 17 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 154 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 228 2 16 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 228
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 228 2 15 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 228 (accept_3_5 29 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 228 2 14 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 228 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 228 2 13 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 228
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 228 2 12 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 228 (accept_3_5 23 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 228 2 11 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 228 (Polychromatic418967fa.accept_27_21_19_12_1_13647 21 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 228 2 10 77 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 228
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 228 2 9 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 228 (accept_3_5 17 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 228 2 8 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 228 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 228 2 7 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 228
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 228 2 6 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 228 (accept_3_5 11 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 228 2 5 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 228 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 154 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 228 2 4 77 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 228
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 228 2 3 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 228 (accept_3_5 5 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  228 2 2 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 228 (Polychromatic418967fa.accept_13_3_11_7_1_2488 3 154 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 228 2 1 77 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 228 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 154 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 153 228 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 153 228 3 25 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 153 228 (Polychromatic418967fa.accept_20_14_13_8_1_4847 74 153 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 153 228 3 24 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 153 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 153 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 228
  (Polychromatic418967fa.accept_18_16_9_12_1_1182 70 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 153 228 3 23 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 153 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 153 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 153 228
  (Polychromatic418967fa.accept_21_4_6_18_1_9132 67 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 153 228 3 22 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 153 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 153 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 228 (Polychromatic418967fa.accept_11_9_10_8_1_444
  64 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 153 228 3 21 51 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 153 228
  (Polychromatic418967fa.accept_16_14_9_4_1_6693 62 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 153 228 3 20 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 153 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 59
  153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 58 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 153 228 3 19 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 153 228 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 153 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 228
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 153 228 3 18 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 153 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 153 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 52
  153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 228 3 17 51 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 228
  (Polychromatic418967fa.accept_23_4_15_21_1_13646 50 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 153 228 (Polychromatic418967fa.accept_21_7_6_18_1_7681 49 153 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 153 228 3 16 51 76 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 153 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 228 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 153 228 3 15 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 153 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 228
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 153 228 3 14 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 153 228 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 153 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 228 (Polychromatic418967fa.accept_7_5_6_4_1_117
  40 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 153 228 3 13 51 76
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 153 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 228 3 12 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 228 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  35 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 228
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 34 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 153 228 3 11 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 228 (Polychromatic418967fa.accept_21_11_6_18_1_4450 32 153 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 153 228 3 10 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 153 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 153 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 228
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 28 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 153 228 3 9 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 153 228 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 228 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 153
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 228 3 8 51 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 228
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 228 (Polychromatic418967fa.accept_18_4_9_12_1_1175 22 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 228 3 7 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 228 (Polychromatic418967fa.accept_11_9_10_8_1_444
  20 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 153 228 3 6 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 153 228 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 153 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 228 3 5 51 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 228
  (Polychromatic418967fa.accept_16_14_9_4_1_6693 14 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 228 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 228 3 4 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 228 (Polychromatic418967fa.accept_10_1_3_8_1_136
  11 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 228
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 153 228 3 3 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 153 228 (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 228 (Polychromatic418967fa.accept_21_7_6_18_1_7681 7 153
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 228 3 2 51 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 228
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 228 (Polychromatic418967fa.accept_13_4_10_7_1_1701 4 153 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 228 3 1 51 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 228 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 153 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 228
  (Polychromatic418967fa.accept_10_1_3_8_1_136 1 153 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 153 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 152 228
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 152 228 76 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 152 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 75 152 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 152 228 2 37 76 114 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 152 228 (accept_3_4 73 152 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 152 228 4 18 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 152 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 71 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 152 228 2 35 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 152 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 152 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 152 228 4 17 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 152 228 (accept_3_4 67 152 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 152 228 2 33 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 152 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 65
  152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 228 4 16 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 228
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 228 2 31 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 228 (accept_3_4 61 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 228 4 15 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 228 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 152 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 228 2 29 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 152 228 19 3 8 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 152 228 4 14 38 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 152 228 (accept_3_4 55 152 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 152 228 2 27 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 152 228
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 53 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 152 228 4 13 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 152 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 152 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 152 228 2 25 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 152 228 (accept_3_4 49 152 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 152 228 4 12 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 152 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 47
  152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 228 2 23 76 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 228
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 228 4 11 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 228 (accept_3_4 43 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 228 2 21 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 152 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 228 4 10 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 228
  (Polychromatic418967fa.accept_16_7_8_4_1_689 39 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 228 38 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 152 228 (accept_3_4 37 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36
  152 228 4 9 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  35 152 228 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 152 228 2 17 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 152 228 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 152 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 228 4 8 38 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 228 (accept_3_4 31 152 228
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 228 2 15 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 228 4 7 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 228 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 152 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 228 2 13 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 228 (accept_3_4 25 152 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 228 4 6 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 152 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 228 2 11 76 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 228
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 228 4 5 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 19 152 228 19 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 152 228 2 9 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 228 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 152 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 228 4 4 38 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 228
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 228 2 7 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 228 (accept_3_4 13 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 228 4 3 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 152 228 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 152 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 228 2 5 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 228 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 228 4 2 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 228 (accept_3_4 7
  152 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 228 2 3 76 114 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 228
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 152 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 152 228 4 1 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 152 228 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 152 228 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 228 2 1 76 114 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 228 (accept_3_4 1 152 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 78 151 228 (Eq.refl Bool.true) (allA_succ_of_accept 77 151 228 (accept_3_5 77 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 151 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 75 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 151 228 (accept_3_5 74 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 73 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 151 228 (Polychromatic418967fa.accept_16_8_7_4_1_2217 72 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 228 (accept_3_5 71 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 228 (Polychromatic418967fa.accept_17_2_15_7_1_6213 70 151
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 228 (accept_3_5 68 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 228 (Polychromatic418967fa.accept_13_1_8_7_1_1088 66 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 228 (accept_3_5 65 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 151 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 228
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 228 (accept_3_5 62 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 228 (Polychromatic418967fa.accept_13_9_8_7_1_1073 61 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 228 (accept_3_5 59 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 228
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 57 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 228 (accept_3_5 56 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 228 (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 228 (accept_3_5 53 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 228 (Polychromatic418967fa.accept_23_6_13_21_1_3511 52 151
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 228 (accept_3_5 50 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 228 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 228 (accept_3_5 47 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 151 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 228
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 228 (accept_3_5 44 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 228 (accept_3_5 41 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 228
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 228 (accept_3_5 38 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 228 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 228 (accept_3_5 35 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 228 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 151
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 228 (accept_3_5 32 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 228 (Polychromatic418967fa.accept_16_14_7_4_1_3243 30 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 228 (accept_3_5 29 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 151 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 228 (accept_3_5 26 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 228 (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 228 (accept_3_5 23 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 228
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 21 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 228 (accept_3_5 20 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 228 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 228 (Polychromatic418967fa.accept_20_18_11_8_1_6367 18 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 228 (accept_3_5 17 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 228 (Polychromatic418967fa.accept_13_3_8_7_1_4135 16 151
  228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 228
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 228 (accept_3_5 14 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 228 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 228 (accept_3_5 11 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 151 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 228
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 228 (accept_3_5 8 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 228 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 228 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 228 (accept_3_5 5 151 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 228 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 151 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 228
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 228 (accept_3_5 2 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 228 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 151 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 228))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 150 228 (Eq.refl Bool.true) (allA_succ_of_gcd 78 150 228 6 13 25 38 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 150 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 150 228 2 38 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 150 228 3 25 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 150 228 2 37 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 150 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 150 228 6 12 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 150 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 150 228 2 35 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 150 228 3 23 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 150 228 2 34 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 150 228 6 11 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 150 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 150 228 2 32 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 150 228 3 21 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 150 228 2 31 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 228 6 10 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 228 2 29 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 150 228 3 19 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 228 2 28 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 150 228 6 9 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 228
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 228 2 26 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 150 228 3 17 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 150 228 2 25 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 228 6 8 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 47 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 228 2 23 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 150 228 3 15 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 228 2 22 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 228 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 150 228 6 7 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 228
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 228 2 20 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 150 228 3 13 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 228 2 19 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 228 6 6 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 150 228
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 228 2 17 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 150 228 3 11 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 228 2 16 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 228 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 150 228
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 228 6 5 25 38 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 228 2 14 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 150 228 3 9 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 150 228 2 13 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 150 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 150 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 228 6 4 25 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 228
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 228 2 11 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 150 228 3 7 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 150 228 2 10 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 228 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 150 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 228 6 3 25 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 228
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 228 2 8 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 150 228 3 5 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 150 228 2 7 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 150 228 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 150 228 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 228 6 2 25 38 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 228
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 228 2 5 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 150 228 3 3 50 76 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 150 228 2 4 75 114 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 150 228 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 228 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 228 6 1 25 38 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 228 (Polychromatic418967fa.accept_9_5_6_3_1_40 5
  150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 228 2 2 75 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 228 3 1 50 76 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 228 2 1 75 114 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 228
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 150 228 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 228)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_228_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


