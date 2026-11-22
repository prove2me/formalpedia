-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch236
-- name    : Polychromatic418967fa_Branch236
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:45.697012+00:00
-- url     : https://prove2.me/theorems/3332aca5-4d2e-44a3-a32a-fa89bdc0e7da
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch236_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_236 : allB 236 236 :=
  allB_succ' 2 235 236 (Eq.refl Bool.true) (allA_of_3_0 2 235 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  234 236 (Eq.refl Bool.true) (allA_succ_of_gcd 2 234 236 2 1 117 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 236 (accept_3_2 1 234 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 234 236))) (allB_succ' 4 233 236 (Eq.refl Bool.true) (allA_succ_of_accept 3 233 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 233 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 233 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 233 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 236 (accept_3_2 1 233 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 233 236)))) (allB_succ' 5 232 236 (Eq.refl Bool.true) (allA_of_3_0 5 232 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 231 236 (Eq.refl Bool.true) (allA_succ_of_accept 5 231 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 231 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 236 (accept_3_2 4 231 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  231 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 231 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 231 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 231 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 236 (accept_3_2 1 231 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 231 236)))))) (allB_succ' 7 230 236 (Eq.refl Bool.true) (allA_succ_of_gcd 6 230 236 2 3
  115 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 230 236
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 230 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 230 236 2 2 115 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 230 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 230 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 230 236 2 1 115 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 230 236 (accept_3_2 1 230 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 230 236))))))) (allB_succ' 8 229 236 (Eq.refl Bool.true) (allA_of_3_0 8 229
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 228 236 (Eq.refl Bool.true) (allA_succ_of_gcd 8 228 236 4 2
  57 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 236
  (accept_3_2 7 228 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 236 2 3 114 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 228 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 228 236 4 1 57 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 228 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 228 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 236 2 1 114 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 236 (accept_3_2 1 228 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 228 236))))))))) (allB_succ' 10 227 236 (Eq.refl Bool.true) (allA_succ_of_accept 9 227
  236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 227 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 227 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 227 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 236 (accept_3_2 7 227 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 227 236 (Polychromatic418967fa.accept_15_6_2_11_1_325 6 227 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 236 (Polychromatic418967fa.accept_14_5_3_12_1_324
  5 227 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 236 (accept_3_2 4
  227 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 227 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 227 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 236 (accept_3_2 1 227 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 227 236)))))))))) (allB_succ' 11 226 236 (Eq.refl Bool.true) (allA_of_3_0 11 226 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 225 236 (Eq.refl Bool.true) (allA_succ_of_accept 11 225 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 225 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 236 (accept_3_2 10 225 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  225 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 225 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 236 (Polychromatic418967fa.accept_16_8_1_12_1_984 8 225 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 236 (accept_3_2 7 225 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 225 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 236 (accept_3_2 4 225 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  225 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 225 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 225 236 (Polychromatic418967fa.accept_16_2_1_12_1_3798 2 225 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 236 (accept_3_2 1 225 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 236)))))))))))) (allB_succ' 13 224 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 224 236 4 3 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 224 236 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 224 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 236 2 5 112 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 236 (Polychromatic418967fa.accept_13_9_3_2_1_399 9
  224 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 236 4 2 56 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 224 236 (accept_3_2 7
  224 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224 236 2 3 112 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 224 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 224 236 4 1 56 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 224 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 224 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 236 2 1 112 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 236 (accept_3_2 1 224 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 236))))))))))))) (allB_succ' 14 223 236 (Eq.refl Bool.true) (allA_of_3_0 14 223 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 222 236 (Eq.refl Bool.true) (allA_succ_of_gcd 14 222 236 2 7
  111 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222
  236 (accept_3_2 13 222 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 236 2 6 111 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 222 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 236 2 5 111 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 222 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 236 2 4 111 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 236 (accept_3_2 7 222 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 222 236 2 3 111 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5
  222 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 236 2 2 111 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 222 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 236 2 1 111 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 236 (accept_3_2 1 222 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  236))))))))))))))) (allB_succ' 16 221 236 (Eq.refl Bool.true) (allA_succ_of_accept 15 221 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 221 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 221 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 221 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 236 (accept_3_2 13 221 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 221 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 221 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 236
  (Polychromatic418967fa.accept_19_11_12_8_1_11492 11 221 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 221 236 (accept_3_2 10 221 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 221 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 221 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 236 (accept_3_2 7 221 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  221 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 236
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 221 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 236 (accept_3_2 4 221 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 221 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 221 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 236 (accept_3_2 1 221 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 236)))))))))))))))) (allB_succ' 17 220 236 (Eq.refl Bool.true) (allA_of_3_0 17 220
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 219 236 (Eq.refl Bool.true) (allA_succ_of_accept 17 219
  236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 236 (accept_3_2 16 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 219 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 236 (accept_3_2 13 219 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 219 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 236 (accept_3_2 10 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 236 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 219 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 236 (accept_3_2 7 219 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 219 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 236 (accept_3_2 4 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 219 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 236 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 219 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 236 (accept_3_2 1 219 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 236)))))))))))))))))) (allB_succ' 19 218 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 218 236 2 9 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 218 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 236 2 8 109 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 236
  (Polychromatic418967fa.accept_20_15_18_16_1_5441 15 218 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 218 236 2 7 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 218 236 (accept_3_2 13 218 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 236 2 6 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 218 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 236 2 5 109 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 236
  (Polychromatic418967fa.accept_27_9_2_20_1_12263 9 218 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 236 2 4 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 236 (accept_3_2 7 218 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 236 2 3 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 218 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 236 2 2 109 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 218 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 236 2 1 109 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 236 (accept_3_2 1 218 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  236))))))))))))))))))) (allB_succ' 20 217 236 (Eq.refl Bool.true) (allA_of_3_0 20 217 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 216 236 (Eq.refl Bool.true) (allA_succ_of_gcd 20 216 236 4 5 54 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 236 (accept_3_2 19 216 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 236 2 9 108 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 236
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 216 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 216 236 4 4 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 216 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 216 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 236 2 7 108 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 236 (accept_3_2 13 216 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 236 4 3 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 216 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 236 2 5 108 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 236
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 216 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 236 4 2 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 216 236 (accept_3_2 7 216 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216
  236 2 3 108 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  216 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 216 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 216 236 4 1 54 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 216 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 216 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 236 2 1 108 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 236 (accept_3_2 1 216 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 236))))))))))))))))))))) (allB_succ' 22 215 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 215 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 236 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 215
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 236 (accept_3_2 19 215
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 236
  (Polychromatic418967fa.accept_13_5_7_2_1_852 18 215 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 215 236 (Polychromatic418967fa.accept_14_3_5_12_1_4000 17 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 236 (accept_3_2 16 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 215 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 215 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 236 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 215 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 236 (accept_3_2 13
  215 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 215 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 215 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 236 (accept_3_2 10 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 215 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 215 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988
  8 215 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 236 (accept_3_2 7
  215 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 215 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 215 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 236 (accept_3_2 4 215 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 215 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 236 (Polychromatic418967fa.accept_12_2_11_8_1_504
  2 215 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 236 (accept_3_2 1
  215 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215 236)))))))))))))))))))))) (allB_succ' 23 214 236
  (Eq.refl Bool.true) (allA_of_3_0 23 214 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 213 236 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 213 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 236 (accept_3_2 22 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 213 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 236
  (Polychromatic418967fa.accept_13_7_5_2_1_401 20 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 236 (accept_3_2 19 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 236 (accept_3_2 16 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 213 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 236 (accept_3_2 13 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 236 (accept_3_2 10 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 213 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 236 (accept_3_2 7 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 236 (accept_3_2 4 213 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 213 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 236 (accept_3_2 1 213 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  236)))))))))))))))))))))))) (allB_succ' 25 212 236 (Eq.refl Bool.true) (allA_succ_of_gcd 24 212 236 4 6 53 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 212 236
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 212 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 212 236 2 11 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 212 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 212 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 212 236 4 5 53 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 212 236 (accept_3_2 19 212 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 212 236 2 9 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 212 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  212 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 236 4 4 53 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 212 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 236 2 7 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 236 (accept_3_2 13 212 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 236 4 3 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 212 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 212 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 236 2 5 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391
  9 212 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 236 4 2 53 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 236 (accept_3_2 7
  212 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 236 2 3 106 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 236
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 212 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 212 236 4 1 53 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 212 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 212 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 236 2 1 106 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 236 (accept_3_2 1 212 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 236))))))))))))))))))))))))) (allB_succ' 26 211 236 (Eq.refl Bool.true)
  (allA_of_3_0 26 211 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 210 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 210 236 2 13 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 210 236 (accept_3_2 25 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 236 2 12 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 210 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 236 2 11 105 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 236 2 10 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 236 (accept_3_2 19 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 236 2 9 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 210 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 236 2 8 105 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 210 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 210 236 2 7 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 236 (accept_3_2 13 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 236 2 6 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 236 (Polychromatic418967fa.accept_19_11_1_8_1_10127 11 210 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 236 2 5 105 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 236 2 4 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 236 (accept_3_2 7 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 236 2 3 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 210 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 236 2 2 105 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 236 2 1 105 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 236 (accept_3_2 1 210 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  236))))))))))))))))))))))))))) (allB_succ' 28 209 236 (Eq.refl Bool.true) (allA_succ_of_accept 27 209 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 209 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 236 (accept_3_2 25 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 209 236 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 209 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 236
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 236 (accept_3_2 22 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 236 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 209 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 236 (accept_3_2 19 209 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 209 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 236
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 209 236 (accept_3_2 16 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 209 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 209
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 236 (accept_3_2 13 209
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 236
  (Polychromatic418967fa.accept_13_12_1_2_1_845 12 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 209 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 236 (accept_3_2 10 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 209 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 8
  209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 236 (accept_3_2 7 209
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 236
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 209 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 236 (accept_3_2 4 209 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 209 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 209 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  209 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 236 (accept_3_2 1 209
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209 236)))))))))))))))))))))))))))) (allB_succ' 29 208 236
  (Eq.refl Bool.true) (allA_of_3_0 29 208 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 207 236 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 207 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 236 (accept_3_2 28 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 207 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 236
  (Polychromatic418967fa.accept_20_6_7_16_1_5437 26 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 236 (accept_3_2 25 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 236 (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 236 (accept_3_2 22 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 207 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 236 (accept_3_2 19 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 236 (accept_3_2 16 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 207 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 236
  (Polychromatic418967fa.accept_13_1_12_2_1_384 14 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 236 (accept_3_2 13 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 236 (Polychromatic418967fa.accept_17_12_3_15_1_5476 12 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 236 (accept_3_2 10 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 207 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 236 (accept_3_2 7 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 236 (accept_3_2 4 207 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 207 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 236 (accept_3_2 1 207 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  236)))))))))))))))))))))))))))))) (allB_succ' 31 206 236 (Eq.refl Bool.true) (allA_succ_of_gcd 30 206 236 2 15 103 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 206 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 206 236 2 14 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 206 236 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 206 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 206 236 2 13 103 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 206 236 (accept_3_2 25 206 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 206 236 2 12 103 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 206 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 206 236 2 11 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 206 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 206 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 206 236 2 10 103 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 206 236 (accept_3_2 19 206 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 206 236 2 9 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 206 236 (Polychromatic418967fa.accept_12_5_2_8_1_172
  17 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 236 2 8 103 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 236 2 7 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 236 (accept_3_2 13 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 236 2 6 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 206 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 236 2 5 103 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 236 2 4 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 236 (accept_3_2 7 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 236 2 3 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 206 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 236 2 2 103 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 236 2 1 103 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 236 (accept_3_2 1 206 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  236))))))))))))))))))))))))))))))) (allB_succ' 32 205 236 (Eq.refl Bool.true) (allA_of_3_0 32 205 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 204 236 (Eq.refl Bool.true) (allA_succ_of_gcd 32 204 236 4 8 51 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 236
  (accept_3_2 31 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 236 2 15 102 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 236
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 236 4 7 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 204 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 204 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 236 2 13 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 236 (accept_3_2 25 204 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 236 4 6 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 204 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 236 2 11 102 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 236 4 5 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 204 236 (accept_3_2 19 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  204 236 2 9 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 204 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 236 4 4 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 236 (Polychromatic418967fa.accept_10_5_4_6_1_319
  15 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 236 2 7 102 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 236
  (accept_3_2 13 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 236 4 3 51 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 236 2 5 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 236 (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 204 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 236 4 2 51 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 236 (accept_3_2 7 204 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 236 2 3 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 204 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 236 4 1 51 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 236 2 1 102 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 236 (accept_3_2 1 204 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  236))))))))))))))))))))))))))))))))) (allB_succ' 34 203 236 (Eq.refl Bool.true) (allA_succ_of_accept 33 203 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 203 236 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 236 (accept_3_2 31 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 203 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 203 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 236 (Polychromatic418967fa.accept_10_9_3_6_1_686
  29 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 236 (accept_3_2 28
  203 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 203 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 236 (accept_3_2 25 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 203 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 203 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 236 (Polychromatic418967fa.accept_8_7_3_4_1_404
  23 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 236 (accept_3_2 22
  203 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 203 236 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 236 (accept_3_2 19 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 203 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 203 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 236 (accept_3_2 16 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 203 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 236 (accept_3_2 13 203 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 203 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 236
  (Polychromatic418967fa.accept_17_11_16_15_1_5467 11 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 203 236 (accept_3_2 10 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 203 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 203 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 203 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 236 (accept_3_2 7 203 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 236
  (Polychromatic418967fa.accept_14_5_7_12_1_4006 5 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 236 (accept_3_2 4 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 203 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 236 (accept_3_2 1 203 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 236)))))))))))))))))))))))))))))))))) (allB_succ' 35 202 236 (Eq.refl Bool.true)
  (allA_of_3_0 35 202 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 201 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 201 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 201 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 236 (accept_3_2 34 201 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 201 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 236 (Polychromatic418967fa.accept_9_5_3_2_1_171
  32 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 236 (accept_3_2 31
  201 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 236
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 236 (accept_3_2 28 201 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 201 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 236 (accept_3_2 25 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 236 (accept_3_2 22 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 201 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 236
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 236 (accept_3_2 19 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 236 (accept_3_2 16 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 201 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 236 (accept_3_2 13 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 236 (accept_3_2 10 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 236 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 201 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 236 (accept_3_2 7 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 236 (accept_3_2 4 201 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 236 (Polychromatic418967fa.accept_14_3_5_12_1_4000 3 201 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 236 (accept_3_2 1 201 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  236)))))))))))))))))))))))))))))))))))) (allB_succ' 37 200 236 (Eq.refl Bool.true) (allA_succ_of_gcd 36 200 236 4 9 50
  59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 200 236
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 200 236 2 17 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 200 236 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 200 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 236 4 8 50 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 236 (accept_3_2 31 200 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 236 2 15 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 236 4 7 50 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 236 2 13 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 200 236 (accept_3_2 25 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 236 4 6 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 200 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 200 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 236 2 11 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 236 (Polychromatic418967fa.accept_15_6_5_11_1_2378
  21 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 236 4 5 50 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 236
  (accept_3_2 19 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 236 2 9 100 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 236
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 200 236 4 4 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 200 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 200 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 236 2 7 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 236 (accept_3_2 13 200 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 236 4 3 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 236 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 200
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 236 2 5 100 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 236 4 2 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 200 236 (accept_3_2 7 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200
  236 2 3 100 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  200 236 (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 200 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 200 236 4 1 50 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 200 236 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 200 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 236 2 1 100 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 236 (accept_3_2 1 200 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 200 236))))))))))))))))))))))))))))))))))))) (allB_succ' 38 199 236 (Eq.refl
  Bool.true) (allA_of_3_0 38 199 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 198 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 198 236 2 19 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 236 (accept_3_2 37 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 236 2 18 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 236 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 198 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 236 2 17 99 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 236 2 16 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 236 (accept_3_2 31 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 236 2 15 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 236 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 198 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 236 2 14 99 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 236 2 13 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 236 (accept_3_2 25 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 236 2 12 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 198 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 236 2 11 99 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 236 2 10 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 236 (accept_3_2 19 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 236 2 9 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 198 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 236 2 8 99 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 236 2 7 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 236 (accept_3_2 13 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 236 2 6 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 198 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 236 2 5 99 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 236 2 4 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 236 (accept_3_2 7 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  236 2 3 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 236 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 198 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 236 2 2 99 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 198 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 236 2 1 99 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 236 (accept_3_2 1 198 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 236))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 197
  236 (Eq.refl Bool.true) (allA_succ_of_accept 39 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 236 (accept_3_2 37 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 236 (Polychromatic418967fa.accept_15_6_2_11_1_325 36 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 236 (accept_3_2 34 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 236 (accept_3_2 31 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 236 (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 236 (accept_3_2 28 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 197 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 236
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 236 (accept_3_2 25 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 236 (accept_3_2 22 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 236 (accept_3_2 19 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 236 (accept_3_2 16 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 236 (accept_3_2 13 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 236 (accept_3_2 10 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 236
  (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 236 (accept_3_2 7 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 236 (accept_3_2 4 197 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 197 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 236 (accept_3_2 1 197 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  236)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 196 236 (Eq.refl Bool.true) (allA_of_3_0 41 196 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 195 236 (Eq.refl Bool.true) (allA_succ_of_accept 41 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 236 (accept_3_2 40 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 236 (Polychromatic418967fa.accept_20_18_15_16_1_9893 38 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 236 (accept_3_2 37 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 195 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 236 (accept_3_2 34 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 236 (Polychromatic418967fa.accept_19_14_5_8_1_10077 33 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 236 (accept_3_2 31 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 236 (accept_3_2 28 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 236 (Polychromatic418967fa.accept_17_10_8_15_1_8104 27 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 236 (accept_3_2 25 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 236 (accept_3_2 22 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 236 (Polychromatic418967fa.accept_14_6_13_12_1_810 20 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 236 (accept_3_2 19 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 195 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 236 (accept_3_2 16 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 236 (accept_3_2 13 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 236 (accept_3_2 10 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 236 (accept_3_2 7 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 195 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 236 (accept_3_2 4 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 195 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 236 (accept_3_2 1 195 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 236)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 194 236 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 194 236 2 21 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 194 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 194 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 236 2 20 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 236 2 19 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 236 (accept_3_2 37 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 236 2 18 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 194 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 236 2 17 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 236 2 16 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 236 (accept_3_2 31 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 236 2 15 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 194 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 236 2 14 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 236
  (Polychromatic418967fa.accept_13_1_12_2_1_384 27 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 236 2 13 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 236 (accept_3_2 25 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 236 2 12 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 194 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 236 2 11 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 236 2 10 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 236 (accept_3_2 19 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 236 2 9 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 194 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 236 2 8 97 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 236 2 7 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 236 (accept_3_2 13 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 236 2 6 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 194 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 236 2 5 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 236
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 236 2 4 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 236 (accept_3_2 7 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  236 2 3 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 194 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 236 2 2 97 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 194 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 236 2 1 97 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 236 (accept_3_2 1 194 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 236))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  193 236 (Eq.refl Bool.true) (allA_of_3_0 44 193 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 192 236
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 192 236 4 11 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 236 (accept_3_2 43 192 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 192 236 2 21 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 192 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 192 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 236 4 10 48 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 236
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 236 2 19 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 236 (accept_3_2 37 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 236 4 9 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 192 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 192 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 236 2 17 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 236 4 8 48 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 236 (accept_3_2 31
  192 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 236 2 15 96 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 192 236 4 7 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 192 236 (Polychromatic418967fa.accept_17_10_5_15_1_4332 27 192 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 236 2 13 96 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 236 (accept_3_2 25 192 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 236 4 6 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 236 2 11 96 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 192 236 4 5 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 192 236 (accept_3_2 19 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  192 236 2 9 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 192 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 236 4 4 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 236 2 7 96 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 236 (accept_3_2 13
  192 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 236 4 3 48 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 236 2 5 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 192 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 192 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 236 4 2 48 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 236 (accept_3_2 7 192 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 236 2 3 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 192 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 236 4 1 48 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 192 236
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 192 236 2 1 96 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 192 236 (accept_3_2 1 192 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  236))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 191 236 (Eq.refl Bool.true) (allA_succ_of_accept 45
  191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 236 (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 191 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 236 (accept_3_2 43 191 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 191
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 236
  (Polychromatic418967fa.accept_20_1_11_16_1_699 41 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 236 (accept_3_2 40 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 236 (accept_3_2 37 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 236 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 191 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 236 (accept_3_2 34 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 236 (accept_3_2 31 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 236 (Polychromatic418967fa.accept_19_11_1_8_1_10127 30 191 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 236
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 236 (accept_3_2 28 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 191 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 236 (accept_3_2 25 191 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 191 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 236
  (Polychromatic418967fa.accept_22_1_15_16_1_14154 23 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 191 236 (accept_3_2 22 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 191 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 236 (Polychromatic418967fa.accept_13_7_9_2_1_2167 20 191
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 236 (accept_3_2 19 191
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 191 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 191 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 236 (accept_3_2 16 191 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 236 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 236 (accept_3_2 13
  191 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 191 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 191 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 236 (accept_3_2 10 191 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 236
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 236 (accept_3_2 7 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 236 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 236 (accept_3_2 4 191 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 236 (accept_3_2 1 191 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  236)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 190 236 (Eq.refl Bool.true) (allA_of_3_0 47 190 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 189 236 (Eq.refl Bool.true) (allA_succ_of_accept 47 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 236 (accept_3_2 46 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 236 (Polychromatic418967fa.accept_13_5_7_2_1_852 44 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 236 (accept_3_2 43 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 189
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 236 (accept_3_2 40 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 236 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 236 (Polychromatic418967fa.accept_17_4_2_15_1_1254 38 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 236 (accept_3_2 37 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 236 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 189
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 236 (accept_3_2 34 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 236 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 236 (accept_3_2 31 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 189
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 236 (accept_3_2 28 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 236 (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 236 (Polychromatic418967fa.accept_16_10_13_12_1_4873 26 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 236 (accept_3_2 25 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 236 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 189
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 236 (accept_3_2 22 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 236 (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 236 (accept_3_2 19 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 189
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 236 (accept_3_2 16 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 236 (Polychromatic418967fa.accept_22_14_13_16_1_14137 14 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 236 (accept_3_2 13 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 236 (Polychromatic418967fa.accept_25_12_14_11_1_14153 12
  189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 236 (accept_3_2 10 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 236 (Polychromatic418967fa.accept_11_8_2_5_1_1769 8 189 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 236 (accept_3_2 7 189 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 236 (accept_3_2 4 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 189 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 236 (accept_3_2 1 189 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 236)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 188
  236 (Eq.refl Bool.true) (allA_succ_of_gcd 48 188 236 4 12 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 188 236 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 188 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 236 2 23 94 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 236
  (Polychromatic418967fa.accept_22_1_12_16_1_6178 45 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 188 236 4 11 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 188 236 (accept_3_2 43 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 236 2 21 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 188 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 236 4 10 47 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 236 2 19 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 236 (accept_3_2 37 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 236 4 9 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 188 236 (Polychromatic418967fa.accept_13_9_6_2_1_2200 35 188 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 236 2 17 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 236 4 8 47 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 236 (accept_3_2 31
  188 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 236 2 15 94 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 188 236 4 7 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 188 236 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 188 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 236 2 13 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 236 (accept_3_2 25 188 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 236 4 6 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 188 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 236 2 11 94 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 236 4 5 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 188 236 (accept_3_2 19 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  188 236 2 9 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 188 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 188 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 236 4 4 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 236 2 7 94 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 236 (accept_3_2 13
  188 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 236 4 3 47 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 188 236 2 5 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 188 236 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 188 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 236 4 2 47 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 236 (accept_3_2 7 188 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 236 2 3 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 188 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 188 236 4 1 47 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 188 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 188 236 2 1 94 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 188 236 (accept_3_2 1 188 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  236))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 187 236 (Eq.refl Bool.true) (allA_of_3_0 50 187
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 186 236 (Eq.refl Bool.true) (allA_succ_of_gcd 50 186 236 2
  25 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186
  236 (accept_3_2 49 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 186 236 2 24 93 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 186 236
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 186 236 2 23 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 186 236 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 186 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 186 236 2 22 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 236 (accept_3_2 43 186 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 186 236 2 21 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 186 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41
  186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 236 2 20 93 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 236 2 19 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 236 (accept_3_2 37 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 236 2 18 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 186 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 236 2 17 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 236 2 16 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 236 (accept_3_2 31 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 236 2 15 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 186 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 236 2 14 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 236 2 13 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 236 (accept_3_2 25 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 236 2 12 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 186 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 236 2 11 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 236 2 10 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 236 (accept_3_2 19 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 236 2 9 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 186 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 236 2 8 93 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 236 2 7 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 236 (accept_3_2 13 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 236 2 6 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 236 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 186 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 236 2 5 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 236 2 4 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 236 (accept_3_2 7 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  236 2 3 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 186 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 236 2 2 93 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 186 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 236 2 1 93 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 236 (accept_3_2 1 186 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 236)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 185 236 (Eq.refl Bool.true) (allA_succ_of_accept 51 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 236 (accept_3_2 49 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 236 (Polychromatic418967fa.accept_14_5_3_12_1_324 47 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 236 (accept_3_2 46 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 185 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 236 (accept_3_2 43 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 41 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 236 (accept_3_2 40 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 185 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 236 (accept_3_2 37 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 236 (accept_3_2 34 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 236
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 236 (accept_3_2 31 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 236 (accept_3_2 28 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 236 (accept_3_2 25 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 236 (accept_3_2 22 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 236
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 236 (accept_3_2 19 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 236 (accept_3_2 16 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 236 (accept_3_2 13 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 236 (accept_3_2 10 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 236 (accept_3_2 7 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 236 (accept_3_2 4 185 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 236 (accept_3_2 1 185 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  236)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 184 236 (Eq.refl Bool.true) (allA_of_3_0 53 184
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 183 236 (Eq.refl Bool.true) (allA_succ_of_accept 53 183
  236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 183 236 (accept_3_2 52 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 183 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 183 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 236 (accept_3_2 49 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 236 (accept_3_2 46 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 183 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 183 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 236 (accept_3_2 43 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 236 (accept_3_2 40 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 183 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 236 (accept_3_2 37 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 236 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 236 (accept_3_2 34 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 236 (accept_3_2 31 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 236 (accept_3_2 28 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 236 (accept_3_2 25 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 236 (accept_3_2 22 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 236 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 236 (accept_3_2 19 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 236 (accept_3_2 16 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 236 (accept_3_2 13 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 236 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 236 (accept_3_2 10 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 236 (accept_3_2 7 183 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 236 (accept_3_2 4 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 183 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 236 (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 236 (accept_3_2 1 183 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 236)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55
  182 236 (Eq.refl Bool.true) (allA_succ_of_gcd 54 182 236 2 27 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 182 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 182 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 236 2 26 91 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 236 2 25 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 182 236 (accept_3_2 49 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 236 2 24 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 182 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 236 2 23 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 236
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 182 236 2 22 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 182 236 (accept_3_2 43 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 236 2 21 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 182 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 236 2 20 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 236
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 236 2 19 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 236 (accept_3_2 37 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 236 2 18 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 182 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 236 2 17 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 236
  (Polychromatic418967fa.accept_21_12_14_5_1_8204 33 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 182 236 2 16 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 182 236 (accept_3_2 31 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 236 2 15 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 182 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 236 2 14 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 236
  (Polychromatic418967fa.accept_23_4_21_6_1_9279 27 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 236 2 13 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 236 (accept_3_2 25 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 236 2 12 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 182 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 236 2 11 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 236 2 10 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 236 (accept_3_2 19 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 236 2 9 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 182 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 236 2 8 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 236
  (Polychromatic418967fa.accept_21_15_14_5_1_9783 15 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 236 2 7 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 236 (accept_3_2 13 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 236 2 6 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 182 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 236 2 5 91 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 236
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 236 2 4 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 236 (accept_3_2 7 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  236 2 3 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 182 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 236 2 2 91 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 236 (Polychromatic418967fa.accept_17_3_12_15_1_1203 3 182 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 236 2 1 91 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 236 (accept_3_2 1 182 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 181 236 (Eq.refl Bool.true) (allA_of_3_0 56 181 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 180 236 (Eq.refl Bool.true) (allA_succ_of_gcd 56 180 236 4 14 45 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 180 236 (accept_3_2 55 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 180 236 2 27 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 180 236 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  53 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 236 4 13 45 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 236
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 51 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 180 236 2 25 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 180 236 (accept_3_2 49 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 236 4 12 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 236 (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 236 2 23 90 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 180 236
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 180 236 4 11 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 180 236 (accept_3_2 43 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 236 2 21 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 236 (Polychromatic418967fa.accept_16_9_4_12_1_4896 41 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 236 4 10 45 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 236
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 180 236 2 19 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 180 236 (accept_3_2 37 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 236 4 9 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 236 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 180 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 236 2 17 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 236 (Polychromatic418967fa.accept_16_1_4_12_1_376
  33 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 236 4 8 45 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 236
  (accept_3_2 31 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 236 2 15 90 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 236
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 236 4 7 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 180 236 (Polychromatic418967fa.accept_16_11_4_12_1_1760 27 180 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 236 2 13 90 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 236 (accept_3_2 25 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 180 236 4 6 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 236
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 180 236 2 11 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 180 236 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 236 4 5 45 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 236 (accept_3_2 19 180 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 236 2 9 90 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 236
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 236 4 4 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 180 236 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 180 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 236 2 7 90 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 236 (accept_3_2 13 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 236 4 3 45 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 236
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 180 236 2 5 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 180 236 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 236 4 2 45 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 236 (accept_3_2 7 180 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 236 2 3 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 236 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  5 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 236 4 1 45 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 236
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 180 236 2 1 90 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 236 (accept_3_2 1 180 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 179 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 179 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 236 (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 179
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 236 (accept_3_2 55 179
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 236
  (Polychromatic418967fa.accept_21_12_11_5_1_6549 54 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 179 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 53 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 236 (accept_3_2 52 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 179 236 (accept_3_2 49 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 179 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 179 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 236 (accept_3_2 46 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 179 236 (accept_3_2 43 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 179 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 179 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 236 (accept_3_2 40 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 236 (accept_3_2 37 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 35 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 236 (accept_3_2 34 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 179 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 236 (accept_3_2 31 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 236 (accept_3_2 28 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 236 (accept_3_2 25 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 236 (accept_3_2 22 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 236 (accept_3_2 19 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 236 (Polychromatic418967fa.accept_20_17_19_16_1_6996 17 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 236 (accept_3_2 16 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 236 (accept_3_2 13 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 236 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 236 (accept_3_2 10 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 236 (accept_3_2 7 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 236 (accept_3_2 4 179 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 236 (accept_3_2 1 179 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 178 236 (Eq.refl Bool.true) (allA_of_3_0
  59 178 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 177 236 (Eq.refl Bool.true) (allA_succ_of_gcd 59
  177 236 59 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  58 177 236 (accept_3_2 58 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 177 236 (Polychromatic418967fa.accept_16_8_1_12_1_984 56 177 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 236 (accept_3_2 55 177 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 177 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 236 (accept_3_2 52 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 177 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 51 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 177 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 236 (accept_3_2 49 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 236 (accept_3_2 46 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 236 (accept_3_2 43 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 236 (accept_3_2 40 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 236 (accept_3_2 37 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 236 (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 177 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 236 (accept_3_2 34 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 33 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 236 (accept_3_2 31 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 236 (accept_3_2 28 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 236 (Polychromatic418967fa.accept_16_11_1_12_1_1795 27 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 236 (accept_3_2 25 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 236 (accept_3_2 22 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 236 (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 236 (accept_3_2 19 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 177 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 236 (accept_3_2 16 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 236 (Polychromatic418967fa.accept_21_15_9_5_1_6588 15 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 236 (accept_3_2 13 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 236 (accept_3_2 10 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 236 (Polychromatic418967fa.accept_17_9_7_15_1_4346 9 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 236 (accept_3_2 7 177 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 236 (accept_3_2 4 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 177 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 236 (Polychromatic418967fa.accept_16_2_1_12_1_3798 2 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 236 (accept_3_2 1 177 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 176 236 (Eq.refl Bool.true) (allA_succ_of_gcd 60 176 236 4 15 44 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 176 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 59 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 176 236 2 29 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 176 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 176 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 176 236 4 14 44 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 176 236 (accept_3_2 55 176 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 176 236 2 27 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53
  176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 176 236 4 13 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 176 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 176 236 2 25 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 176 236 (accept_3_2 49 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 176 236 4 12 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 176 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 176 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 236 2 23 88 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 236 4 11 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 236 (accept_3_2 43 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 236 2 21 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 176 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 236 4 10 44 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 236 2 19 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 236 (accept_3_2 37 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 236 4 9 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 176 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 236 2 17 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 33
  176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 236 4 8 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 236 (accept_3_2 31
  176 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 236 2 15 88 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 236
  (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 176 236 4 7 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 176 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 176 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 236 2 13 88 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 236 (accept_3_2 25 176 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 236 4 6 44 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 236
  (Polychromatic418967fa.accept_19_4_5_8_1_11520 23 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 176 236 2 11 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 176 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 176 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 236 4 5 44 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 236 (accept_3_2 19 176 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 236 2 9 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17
  176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 236 4 4 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 236 2 7 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 236 (accept_3_2 13 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 236 4 3 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 176 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 176 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 236 2 5 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 236 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9
  176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 236 4 2 44 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 236 (accept_3_2 7
  176 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 236 2 3 88 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 236
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 176 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 176 236 4 1 44 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 176 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 236 2 1 88 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 236 (accept_3_2 1 176 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176 236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 175
  236 (Eq.refl Bool.true) (allA_of_3_0 62 175 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 174 236
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 174 236 2 31 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 174 236 (accept_3_2 61 174 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 174 236 2 30 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 174 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 174 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 236 2 29 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 174 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 174 236 2 28 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 236 (accept_3_2 55 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 236 2 27 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 236 2 26 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 236 2 25 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 236 (accept_3_2 49 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 236 2 24 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 236 (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 174 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 236 2 23 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 236 2 22 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 236 (accept_3_2 43 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 236 2 21 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 236 2 20 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 236 2 19 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 236 (accept_3_2 37 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 236 2 18 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 236 2 17 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 236 2 16 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 236 (accept_3_2 31 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 236 2 15 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 236 2 14 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 236 2 13 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 236 (accept_3_2 25 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 236 2 12 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 236 2 11 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 236 2 10 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 236 (accept_3_2 19 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 236 2 9 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 236 2 8 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 236 2 7 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 236 (accept_3_2 13 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 236 2 6 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 174 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 236 2 5 87 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 236 2 4 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 236 (accept_3_2 7 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  236 2 3 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 174 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 236 2 2 87 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 174 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 236 2 1 87 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 236 (accept_3_2 1 174 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 173 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 173 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 173
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 236 (accept_3_2 61 173
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 236
  (Polychromatic418967fa.accept_24_12_5_20_1_14152 60 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 59 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 236 (accept_3_2 58 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 173 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 236
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 56 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 173 236 (accept_3_2 55 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 173 236 (Polychromatic418967fa.accept_23_8_12_6_1_14151 54 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 236
  (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 173 236 (accept_3_2 52 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 173 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 173
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 236 (accept_3_2 49 173
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 173 236 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 173 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 236 (accept_3_2 46 173 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 236 (Polychromatic418967fa.accept_13_5_4_2_1_846
  44 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 236 (accept_3_2 43
  173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 236
  (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 236 (accept_3_2 40 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 236 (accept_3_2 37 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 236 (accept_3_2 34 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 236
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 236 (accept_3_2 31 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 236 (Polychromatic418967fa.accept_19_11_2_8_1_8802 30 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 29 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 236 (accept_3_2 28 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 173 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 236 (accept_3_2 25 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 236 (Polychromatic418967fa.accept_20_3_13_16_1_641 23 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 236 (accept_3_2 22 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 236
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 236 (accept_3_2 19 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 236 (accept_3_2 16 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 236
  (Polychromatic418967fa.accept_11_3_8_5_1_336 14 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 236 (accept_3_2 13 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 236 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 236 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 236 (accept_3_2 10 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 236 (accept_3_2 7 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 236 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 236 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 236 (accept_3_2 4 173 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 236
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 236 (accept_3_2 1 173 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 172 236 (Eq.refl Bool.true)
  (allA_of_3_0 65 172 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 171 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 236 (accept_3_2 64 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 171 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 236 (Polychromatic418967fa.accept_10_2_1_6_1_634
  62 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 236 (accept_3_2 61
  171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 236
  (Polychromatic418967fa.accept_17_9_1_15_1_3156 60 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 236 (accept_3_2 58 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 171 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 171 236 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  56 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 236 (accept_3_2 55
  171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 236
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 171 236 (accept_3_2 52 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 171 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 50
  171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 236 (accept_3_2 49
  171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 236
  (Polychromatic418967fa.accept_15_3_6_11_1_855 48 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 171 236 (accept_3_2 46 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 236 (accept_3_2 43 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 171 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 236 (accept_3_2 40 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 236
  (Polychromatic418967fa.accept_20_18_11_16_1_6973 38 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 171 236 (accept_3_2 37 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 171 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 236 (accept_3_2 34 171 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 236 (Polychromatic418967fa.accept_14_5_3_12_1_324
  33 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 236 (accept_3_2 31 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 171 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 236 (accept_3_2 28 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 236
  (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 171 236 (accept_3_2 25 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 171 236 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 236 (accept_3_2 22 171 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 236
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 236 (accept_3_2 19 171 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 236 (accept_3_2 16 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 236 (Polychromatic418967fa.accept_25_14_21_11_1_14150 14 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 236 (accept_3_2 13 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 171
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 236 (accept_3_2 10 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 236 (accept_3_2 7 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 171 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 236 (accept_3_2 4 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 171 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 236 (accept_3_2 1 171 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 170 236 (Eq.refl Bool.true) (allA_succ_of_gcd 66 170 236 2 33 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 170 236 (Polychromatic418967fa.accept_12_5_2_8_1_172
  65 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 236 2 32 85 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 236
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 170 236 2 31 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 170 236 (accept_3_2 61 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 170 236 2 30 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 170 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 170 236 2 29 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 170 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 170 236 2 28 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 170 236 (accept_3_2 55 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 170 236 2 27 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 170 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 236 2 26 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 170 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 170 236 2 25 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 170 236 (accept_3_2 49 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 170 236 2 24 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 170 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 170 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 236 2 23 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 236 2 22 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 236 (accept_3_2 43 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 236 2 21 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 236 2 20 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 236 2 19 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 236 (accept_3_2 37 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 236 2 18 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 170 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 236 2 17 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 236 2 16 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 236 (accept_3_2 31 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 236 2 15 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 236 2 14 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 236
  (Polychromatic418967fa.accept_16_11_10_12_1_4832 27 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 170 236 2 13 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 170 236 (accept_3_2 25 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 236 2 12 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 236 2 11 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 236 2 10 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 236 (accept_3_2 19 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 236 2 9 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 236 2 8 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 236 2 7 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 236 (accept_3_2 13 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 236 2 6 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 170 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 236 2 5 85 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 236
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 236 2 4 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 236 (accept_3_2 7 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  236 2 3 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 170 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 236 2 2 85 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 170 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 236 2 1 85 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 236 (accept_3_2 1 170 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 169 236 (Eq.refl Bool.true)
  (allA_of_3_0 68 169 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 168 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 168 236 4 17 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 168 236 (accept_3_2 67 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 236 2 33 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 236 (Polychromatic418967fa.accept_16_1_8_12_1_405 65 168 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 236 4 16 42 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 168 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 168 236 2 31 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 168 236 (accept_3_2 61 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 236 4 15 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 168 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 236 2 29 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 236 4 14 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 168 236 (accept_3_2 55 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 168 236 2 27 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 168 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 168 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 236 4 13 42 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 236
  (Polychromatic418967fa.accept_15_6_3_11_1_848 51 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 168 236 2 25 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 168 236 (accept_3_2 49 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 236 4 12 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 168 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 168 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 236 2 23 84 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 236
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 168 236 4 11 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 168 236 (accept_3_2 43 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 236 2 21 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 168 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 236 4 10 42 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 236 2 19 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 236 (accept_3_2 37 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 236 4 9 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 168 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 168 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 236 2 17 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 236 (Polychromatic418967fa.accept_10_3_8_6_1_326
  33 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 236 4 8 42 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 236
  (accept_3_2 31 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 236 2 15 84 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 236
  (Polychromatic418967fa.accept_13_3_12_2_1_385 29 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 236 4 7 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 236 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 168 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 236 2 13 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 236 (accept_3_2 25 168 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 236 4 6 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 236 2 11 84 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 236 4 5 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 168 236 (accept_3_2 19 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  168 236 2 9 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 236 4 4 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 236
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 236 2 7 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 236 (accept_3_2 13 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 236 4 3 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 168 236 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 168 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 236 2 5 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 236
  (Polychromatic418967fa.accept_16_9_8_12_1_979 9 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 236 4 2 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 236 (accept_3_2 7 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  236 2 3 84 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 236 4 1 42 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 168 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 236 2 1 84 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 236 (accept_3_2 1 168 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 167 236 (Eq.refl Bool.true) (allA_succ_of_accept 69 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12
  69 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 167 236
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 68 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 167 236 (accept_3_2 67 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 167 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 167 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 236 (accept_3_2 64 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 167 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 167 236 (accept_3_2 61 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 167 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 167 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 236 (accept_3_2 58 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 167 236
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 167 236 (accept_3_2 55 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 167 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 167 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 236 (accept_3_2 52 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 167 236 (accept_3_2 49 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 167 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 167 236 (Polychromatic418967fa.accept_22_3_13_16_1_11144 47 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 236 (accept_3_2 46 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 167 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 236 (accept_3_2 43 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 41 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 236 (accept_3_2 40 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 236 (accept_3_2 37 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 236 (accept_3_2 34 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 236 (accept_3_2 31 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 236 (accept_3_2 28 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 236 (accept_3_2 25 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 236 (accept_3_2 22 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 236
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 236 (accept_3_2 19 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 236 (accept_3_2 16 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 236 (accept_3_2 13 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 236 (accept_3_2 10 167 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 236 (accept_3_2 7 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 236 (accept_3_2 4 167 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 236 (accept_3_2 1 167 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 166 236 (Eq.refl Bool.true)
  (allA_of_3_0 71 166 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 165 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 165 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 165 236 (accept_3_2 70 165 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 165 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 165 236 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 236 (accept_3_2 67
  165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 236
  (Polychromatic418967fa.accept_12_6_9_8_1_165 66 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 165 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 165 236 (accept_3_2 64 165 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 165 236 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 165 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 165 236 (accept_3_2 61 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 165 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 165 236 (accept_3_2 58 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 236
  (Polychromatic418967fa.accept_16_8_5_12_1_3812 56 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 165 236 (accept_3_2 55 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 165 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 236 (accept_3_2 52 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 165 236 (accept_3_2 49 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 165 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 236 (accept_3_2 46 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 236 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 236 (accept_3_2 43 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 165 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 236 (accept_3_2 40 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 236
  (Polychromatic418967fa.accept_20_18_5_16_1_5425 38 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 165 236 (accept_3_2 37 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 165 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 165 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 165 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 236 (accept_3_2 34 165 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 236 (Polychromatic418967fa.accept_8_1_5_4_1_388
  33 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 236 (accept_3_2 31 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 165 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 236 (accept_3_2 28 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 236 (accept_3_2 25 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 165 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 236 (accept_3_2 22 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 236 (accept_3_2 19 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 236 (accept_3_2 16 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 236 (accept_3_2 13 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 236 (accept_3_2 10 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 236 (accept_3_2 7 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 236 (accept_3_2 4 165 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 236 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 165 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 236 (accept_3_2 1 165 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 164 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 164 236 4 18 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 164 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 236 2 35 82 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 236
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 69 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 236 4 17 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 236 (accept_3_2 67 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 236 2 33 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 164 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 236 4 16 41 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 236
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 164 236 2 31 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 164 236 (accept_3_2 61 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 236 4 15 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 236 (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 236 2 29 82 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 236 4 14 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 236 (accept_3_2 55 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 236 2 27 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 236 (Polychromatic418967fa.accept_16_5_4_12_1_3800 53 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 236 4 13 41 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 236 2 25 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 236 (accept_3_2 49 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 236 4 12 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 236 (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 236 2 23 82 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 236 4 11 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 236 (accept_3_2 43 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 236 2 21 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 236 (Polychromatic418967fa.accept_16_9_4_12_1_4896 41 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 236 4 10 41 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 236
  (Polychromatic418967fa.accept_11_6_10_5_1_341 39 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 236 2 19 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 236 (accept_3_2 37 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 236 4 9 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 164 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 236 2 17 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 236 (Polychromatic418967fa.accept_13_7_8_2_1_1483
  33 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 236 4 8 41 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 236
  (accept_3_2 31 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 236 2 15 82 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 164 236 4 7 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 164 236 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 164 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 236 2 13 82 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 236 (accept_3_2 25 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 236 4 6 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 236 2 11 82 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 236
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 236 4 5 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 236 (accept_3_2 19 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 236 2 9 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 17 164 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 236 4 4 41 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15
  164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 236 2 7 82 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 236 (accept_3_2 13
  164 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 236 4 3 41 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 236
  (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 164 236 2 5 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 164 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 236 4 2 41 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 236 (accept_3_2 7 164 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 236 2 3 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5
  164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 236 4 1 41 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 236
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 164 236 2 1 82 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 164 236 (accept_3_2 1 164 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 163 236 (Eq.refl
  Bool.true) (allA_of_3_0 74 163 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 162 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 162 236 2 37 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 236 (accept_3_2 73 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 236 2 36 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 71 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 236 2 35 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 162 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 162 236 2 34 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 236 (accept_3_2 67 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 236 2 33 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 236 (Polychromatic418967fa.accept_16_1_2_12_1_1757 65 162 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 236 2 32 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 236 2 31 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 236 (accept_3_2 61 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 236 2 30 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 236 2 29 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 236
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 236 2 28 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 236 (accept_3_2 55 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 236 2 27 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 236 2 26 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 236 2 25 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 236 (accept_3_2 49 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 236 2 24 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 236 2 23 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 236 2 22 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 236 (accept_3_2 43 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 236 2 21 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 236 2 20 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 236 2 19 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 236 (accept_3_2 37 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 236 2 18 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 162 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 236 2 17 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 236 2 16 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 236 (accept_3_2 31 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 236 2 15 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 236 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 162 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 236 2 14 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 236 2 13 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 236 (accept_3_2 25 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 236 2 12 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 236 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 162 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 236 2 11 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 236 2 10 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 236 (accept_3_2 19 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 236 2 9 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 236 2 8 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 236 2 7 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 236 (accept_3_2 13 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 236 2 6 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 162 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 236 2 5 81 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 236 2 4 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 236 (accept_3_2 7 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  236 2 3 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 236 (Polychromatic418967fa.accept_19_5_10_8_1_8775 5 162 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 236 2 2 81 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 162 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 236 2 1 81 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 236 (accept_3_2 1 162 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 161 236 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 236 (Polychromatic418967fa.accept_12_2_5_8_1_159
  74 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 236 (accept_3_2 73
  161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 161 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 161 236 (Polychromatic418967fa.accept_19_14_9_8_1_7271 71 161 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 236 (accept_3_2 70 161 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 236 (Polychromatic418967fa.accept_9_5_8_2_1_409
  68 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 236 (accept_3_2 67
  161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 161 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 65 161 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 236 (accept_3_2 64 161 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 236 (Polychromatic418967fa.accept_10_2_1_6_1_634
  62 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 236 (accept_3_2 61
  161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 161 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 161 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 236 (accept_3_2 58 161 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 236 (Polychromatic418967fa.accept_13_4_5_2_1_1436
  56 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 236 (accept_3_2 55
  161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 161 236
  (Polychromatic418967fa.accept_19_16_9_8_1_11539 54 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 236 (accept_3_2 52 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 236 (accept_3_2 49 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 47 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 236 (accept_3_2 46 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 236
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 236 (accept_3_2 43 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 236 (accept_3_2 40 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 236 (accept_3_2 37 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 236 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 236 (accept_3_2 34 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 236 (accept_3_2 31 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 236 (accept_3_2 28 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 236 (accept_3_2 25 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 236 (accept_3_2 22 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 236
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 236 (accept_3_2 19 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 236 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 236 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 236 (accept_3_2 16 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 236 (accept_3_2 13 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 236 (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 236 (accept_3_2 10 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 236
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 236 (accept_3_2 7 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 236 (accept_3_2 4 161 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 236 (accept_3_2 1 161 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 160 236 (Eq.refl
  Bool.true) (allA_of_3_0 77 160 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 159 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 159 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 159 236 (accept_3_2 76 159 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 159 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 236 (Polychromatic418967fa.accept_13_9_3_2_1_399
  74 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 236 (accept_3_2 73
  159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 236
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 72 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 236 (accept_3_2 70 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 236 (Polychromatic418967fa.accept_19_12_7_8_1_12860 69 159 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 236 (accept_3_2 67 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 236 (accept_3_2 64 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 236 (accept_3_2 61 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 236 (Polychromatic418967fa.accept_17_9_6_15_1_5454 60 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 236 (accept_3_2 58 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 236
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 159 236 (accept_3_2 55 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 159 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 159 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 159 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 236 (accept_3_2 52 159 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 51
  159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 236 (accept_3_2 49 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 236 (accept_3_2 46 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 236 (accept_3_2 43 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 236 (accept_3_2 40 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 236
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 38 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 236 (accept_3_2 37 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 236 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 236 (accept_3_2 34 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 236 (accept_3_2 31 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 236 (accept_3_2 28 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 236 (accept_3_2 25 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 236 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 236 (accept_3_2 22 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 236
  (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 236 (accept_3_2 19 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 236 (accept_3_2 16 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 236 (accept_3_2 13 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 236 (accept_3_2 10 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 236 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 236 (accept_3_2 7 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 236 (accept_3_2 4 159 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 236
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 236 (accept_3_2 1 159 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 158 236 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 158 236 2 39 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 158 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 158 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 236 2 38 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 236 2 37 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 236 (accept_3_2 73 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 236 2 36 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 236 2 35 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 236 2 34 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 236 (accept_3_2 67 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 236 2 33 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 236 2 32 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 158 236 2 31 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 158 236 (accept_3_2 61 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 236 2 30 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 158 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 236 2 29 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 236 2 28 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 236 (accept_3_2 55 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 236 2 27 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 236 2 26 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 236 2 25 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 236 (accept_3_2 49 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 236 2 24 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 158 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 236 2 23 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 236
  (Polychromatic418967fa.accept_17_11_5_15_1_8144 45 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 158 236 2 22 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 158 236 (accept_3_2 43 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 236 2 21 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 236 2 20 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 236 2 19 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 236 (accept_3_2 37 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 236 2 18 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 236 2 17 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 236 2 16 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 236 (accept_3_2 31 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 236 2 15 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 236 2 14 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 236 2 13 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 236 (accept_3_2 25 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 236 2 12 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 236 2 11 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 236 2 10 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 236 (accept_3_2 19 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 236 2 9 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 158 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 236 2 8 79 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 236 2 7 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 236 (accept_3_2 13 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 236 2 6 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 158 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 236 2 5 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 236 2 4 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 236 (accept_3_2 7 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  236 2 3 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 158 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 236 2 2 79 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 158 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 236 2 1 79 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 236 (accept_3_2 1 158 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 157 236 (Eq.refl
  Bool.true) (allA_of_3_0 80 157 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 156 236 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 156 236 4 20 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 156 236 (accept_3_2 79 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 236 2 39 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 236 4 19 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 236
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 75 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 156 236 2 37 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 156 236 (accept_3_2 73 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 236 4 18 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 236 2 35 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 236 4 17 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 236 (accept_3_2 67 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 236 2 33 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 65 156 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 236 4 16 39 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 236
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 156 236 2 31 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 156 236 (accept_3_2 61 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 236 4 15 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 236 2 29 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 236
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 57 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 236 4 14 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 236 (accept_3_2 55 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 236 2 27 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 236 4 13 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 236 2 25 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 236 (accept_3_2 49 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 236 4 12 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 236 (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 156 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 236 2 23 78 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 236 4 11 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 236 (accept_3_2 43 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 236 2 21 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 236 4 10 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 236 2 19 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 236 (accept_3_2 37 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 236 4 9 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 156 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 236 2 17 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 236 4 8 39 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 236 (accept_3_2 31
  156 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 236 2 15 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 236
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 29 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 156 236 4 7 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 156 236 (Polychromatic418967fa.accept_28_27_16_12_1_8191 27 156 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 236 2 13 78 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 236 (accept_3_2 25
  156 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 236 4 6 39 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 236 2 11 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 156 236 (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 156 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 236 4 5 39 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 236 (accept_3_2 19 156 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 236 2 9 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 236 4 4 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 156 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 156 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 236 2 7 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 236 (accept_3_2 13 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 236 4 3 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 156 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 236 2 5 78 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 236
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 236 4 2 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 236 (accept_3_2 7 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  236 2 3 78 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 156 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 236 4 1 39 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 156 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 236 2 1 78 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 236 (accept_3_2 1 156 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 155 236 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 80
  155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 236 (accept_3_2 79
  155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 236
  (Polychromatic418967fa.accept_17_10_2_15_1_3179 78 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 236 (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 236 (accept_3_2 76 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 155 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 236 (accept_3_2 73 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 236 (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 236 (accept_3_2 70 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 236
  (Polychromatic418967fa.accept_13_3_12_2_1_385 68 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 236 (accept_3_2 67 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 236 (Polychromatic418967fa.accept_16_1_11_12_1_1774 65 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 236 (accept_3_2 64 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 236 (accept_3_2 61 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 236 (accept_3_2 58 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 236
  (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 236 (accept_3_2 55 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 236 (accept_3_2 52 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 236
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 236 (accept_3_2 49 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 236 (accept_3_2 46 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 236 (accept_3_2 43 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 236 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 236 (accept_3_2 40 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 236 (accept_3_2 37 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 236 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 236 (Polychromatic418967fa.accept_18_17_11_2_1_7782 35 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 236 (accept_3_2 34 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 155 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 236 (accept_3_2 31 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 236 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 29 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 236 (accept_3_2 28 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 236 (accept_3_2 25 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 236 (accept_3_2 22 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 236 (accept_3_2 19 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 236 (accept_3_2 16 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 236 (accept_3_2 13 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 236 (Polychromatic418967fa.accept_21_12_8_5_1_5041 12 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 236 (accept_3_2 10 155 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 236
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 236 (accept_3_2 7 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 236 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 236 (accept_3_2 4 155 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 236 (accept_3_2 1 155 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 154 236 (Eq.refl
  Bool.true) (allA_of_3_0 83 154 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 153 236 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 153 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 236 (accept_3_2 82 153 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 153 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 236
  (Polychromatic418967fa.accept_24_8_9_20_1_7244 80 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 153 236 (accept_3_2 79 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 153 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 236 (accept_3_2 76 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 236 (Polychromatic418967fa.accept_18_3_9_2_1_5053 75 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 74 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 236 (accept_3_2 73 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 153 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 72 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 236 (accept_3_2 70 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 68 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 236 (accept_3_2 67 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 236 (accept_3_2 64 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 236 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 153 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 236
  (Polychromatic418967fa.accept_14_6_13_12_1_810 62 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 236 (accept_3_2 61 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 236 (accept_3_2 58 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 236
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 56 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 236 (accept_3_2 55 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 236 (accept_3_2 52 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 236 (Polychromatic418967fa.accept_13_12_10_2_1_1451 51 153 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 236 (accept_3_2 49 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 236 (accept_3_2 46 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 236
  (Polychromatic418967fa.accept_13_5_10_2_1_856 44 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 236 (accept_3_2 43 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 236 (accept_3_2 40 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 236
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 236 (accept_3_2 37 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 236 (accept_3_2 34 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 236 (Polychromatic418967fa.accept_21_12_6_5_1_3484 33 153 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 236 (accept_3_2 31 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 236 (accept_3_2 28 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 236 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 236
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 236 (accept_3_2 25 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 236 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 236 (accept_3_2 22 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 236
  (Polychromatic418967fa.accept_14_6_13_12_1_810 20 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 236 (accept_3_2 19 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 236 (accept_3_2 16 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 236
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 236 (accept_3_2 13 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 236 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 236 (accept_3_2 10 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 236 (accept_3_2 7 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 236 (accept_3_2 4 153 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 236 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 153 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 236
  (Polychromatic418967fa.accept_16_2_9_12_1_46 2 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 236 (accept_3_2 1 153 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 152 236
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 152 236 4 21 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 152 236 (Polychromatic418967fa.accept_13_5_9_2_1_1489 83 152
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 236 2 41 76 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 81 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 236 4 20 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 236 (accept_3_2 79 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 236 2 39 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 236 4 19 38 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 236 2 37 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 236 (accept_3_2 73 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 236 4 18 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 152 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 71 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 236 2 35 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 152 236 4 17 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 152 236 (accept_3_2 67 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 152 236 2 33 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 152 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 236 4 16 38 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 236
  (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 236 2 31 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 236 (accept_3_2 61 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 236 4 15 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 236 2 29 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 236 4 14 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 236 (accept_3_2 55 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 236 2 27 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 236 (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 152 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 236 4 13 38 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 236 2 25 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 236 (accept_3_2 49 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 236 4 12 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 236 (Polychromatic418967fa.accept_16_15_8_12_1_2737 47 152 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 236 2 23 76 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 236
  (Polychromatic418967fa.accept_13_6_9_2_1_838 45 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 236 4 11 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 236 (accept_3_2 43 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 236 2 21 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 236 4 10 38 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 236 2 19 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 236 (accept_3_2 37 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 236 4 9 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 152 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 236 2 17 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 236 4 8 38 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 236 (accept_3_2 31
  152 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 236 2 15 76 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 236
  (Polychromatic418967fa.accept_11_7_9_5_1_338 29 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 236 4 7 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 236 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 152 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 236 2 13 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 236 (accept_3_2 25 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 236 4 6 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 152 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 236 2 11 76 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 236 4 5 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 236 (accept_3_2 19 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 236 2 9 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 236 (Polychromatic418967fa.accept_16_1_8_12_1_405 17 152 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 236 4 4 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 236 2 7 76 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 236 (accept_3_2 13
  152 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 236 4 3 38 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 236 2 5 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 152 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 236 4 2 38 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 236 (accept_3_2 7 152 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 236 2 3 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 236 4 1 38 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 236 2 1 76 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 236 (accept_3_2 1 152 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 151 236
  (Eq.refl Bool.true) (allA_of_3_0 86 151 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 150 236 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 150 236 2 43 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 150 236 (accept_3_2 85 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 236 2 42 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 236 (Polychromatic418967fa.accept_13_5_7_2_1_852 83 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 236 2 41 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 236 2 40 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 236 (accept_3_2 79 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 236 2 39 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 236 2 38 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 150 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 150 236 2 37 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 236 (accept_3_2 73 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 236 2 36 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 236 2 35 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 236 2 34 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 236 (accept_3_2 67 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 236 2 33 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 236 2 32 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 236 2 31 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 236 (accept_3_2 61 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 236 2 30 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 236 2 29 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 236 2 28 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 236 (accept_3_2 55 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 236 2 27 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 236 2 26 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 236 2 25 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 236 (accept_3_2 49 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 236 2 24 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 150 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 236 2 23 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 236 2 22 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 236 (accept_3_2 43 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 236 2 21 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 236 2 20 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 236 2 19 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 236 (accept_3_2 37 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 236 2 18 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 236 2 17 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 236 2 16 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 236 (accept_3_2 31 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 236 2 15 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 236 2 14 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 236 2 13 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 236 (accept_3_2 25 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 236 2 12 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 236 2 11 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 236 2 10 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 236 (accept_3_2 19 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 236 2 9 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 236 2 8 75 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 236 2 7 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 236 (accept_3_2 13 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 236 2 6 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 236 (Polychromatic418967fa.accept_19_11_17_8_1_7259 11 150 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 236 2 5 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 236 2 4 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 236 (accept_3_2 7 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  236 2 3 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 150 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 236 2 2 75 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 236 2 1 75 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 236 (accept_3_2 1 150 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 149 236
  (Eq.refl Bool.true) (allA_succ_of_accept 87 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 149 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 149 236 (accept_3_2 85 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 149 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 149 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 83 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 149 236 (accept_3_2 82 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 149 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 149 236 (accept_3_2 79 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 149 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 149 236 (Polychromatic418967fa.accept_13_12_6_2_1_1441 77 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 149 236 (accept_3_2 76 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 149 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 149 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 149 236 (accept_3_2 73 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 149 236 (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 236 (accept_3_2 70 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 236
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 68 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 149 236 (accept_3_2 67 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 149 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 149 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 236 (accept_3_2 64 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 236 (accept_3_2 61 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 149 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 236 (accept_3_2 58 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 236
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 56 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 236 (accept_3_2 55 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 236 (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 236 (accept_3_2 52 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 236 (accept_3_2 49 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 236 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 236 (accept_3_2 46 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 236 (accept_3_2 43 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 236 (accept_3_2 40 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 236 (accept_3_2 37 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 236 (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 236 (accept_3_2 34 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 236 (accept_3_2 31 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 236 (Polychromatic418967fa.accept_19_10_16_8_1_3289 29 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 236 (accept_3_2 28 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 236 (accept_3_2 25 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 236 (accept_3_2 22 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 236
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 236 (accept_3_2 19 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 236 (accept_3_2 16 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 236 (accept_3_2 13 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 236 (accept_3_2 10 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 236 (accept_3_2 7 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 5 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 236 (accept_3_2 4 149 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 236 (accept_3_2 1 149 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 148 236
  (Eq.refl Bool.true) (allA_of_3_0 89 148 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 147 236 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 147 236 (accept_3_2 88 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 147 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 87 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 147 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 86 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 147 236 (accept_3_2 85 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 147 236 (Polychromatic418967fa.accept_13_6_4_2_1_1433 84 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 147 236 (accept_3_2 82 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 147 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 81 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 147 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 147 236 (accept_3_2 79 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 147 236 (accept_3_2 76 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 236 (Polychromatic418967fa.accept_14_5_7_12_1_4006 75 147 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 236
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 74 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 147 236 (accept_3_2 73 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 147 236 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 147 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 236 (accept_3_2 70 147 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431
  69 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 147 236 (accept_3_2 67 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 147 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 236 (accept_3_2 64 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 236 (accept_3_2 61 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 236 (accept_3_2 58 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 236 (Polychromatic418967fa.accept_13_5_4_2_1_846 57 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 236
  (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 147 236 (accept_3_2 55 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 147 236 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 236 (accept_3_2 52 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 147 236 (accept_3_2 49 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 147 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 236 (accept_3_2 46 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 236 (Polychromatic418967fa.accept_13_6_4_2_1_1433 45 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 236 (accept_3_2 43 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 236 (accept_3_2 40 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 236
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 236 (accept_3_2 37 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 236 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 236 (accept_3_2 34 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 236 (accept_3_2 31 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 147 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 236 (accept_3_2 28 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 236 (Polychromatic418967fa.accept_18_9_3_2_1_3814 27 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 236 (accept_3_2 25 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 236 (accept_3_2 22 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 236
  (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 236 (accept_3_2 19 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 147 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 236 (accept_3_2 16 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 236 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 236
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 236 (accept_3_2 13 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 147 236 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 236 (accept_3_2 10 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 236 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 236
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 236 (accept_3_2 7 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  147 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 147 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 236 (accept_3_2 4 147 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 236 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 236
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 2 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 236 (accept_3_2 1 147 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 146 236
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 146 236 2 45 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 146 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 146 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 236 2 44 73 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 236
  (Polychromatic418967fa.accept_13_9_3_2_1_399 87 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 236 2 43 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 236 (accept_3_2 85 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 236 2 42 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 146 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 236 2 41 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 236 2 40 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 236 (accept_3_2 79 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 236 2 39 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 236 2 38 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 236
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 75 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 146 236 2 37 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 146 236 (accept_3_2 73 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 236 2 36 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 236 2 35 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 236
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 69 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 146 236 2 34 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 146 236 (accept_3_2 67 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 236 2 33 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 236 2 32 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 236
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 146 236 2 31 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 146 236 (accept_3_2 61 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 236 2 30 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 146 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 236 2 29 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 236 2 28 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 236 (accept_3_2 55 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 236 2 27 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 236 2 26 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 236
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 236 2 25 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 236 (accept_3_2 49 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 236 2 24 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 146 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 236 2 23 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 236
  (Polychromatic418967fa.accept_27_18_11_20_1_4405 45 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 146 236 2 22 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 146 236 (accept_3_2 43 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 236 2 21 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 236 (Polychromatic418967fa.accept_11_8_3_5_1_355 41 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 236 2 20 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 236 2 19 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 236 (accept_3_2 37 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 236 2 18 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 146 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 236 2 17 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 236
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 236 2 16 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 236 (accept_3_2 31 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 236 2 15 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 236 2 14 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 236
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 236 2 13 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 236 (accept_3_2 25 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 236 2 12 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 146 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 236 2 11 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 236
  (Polychromatic418967fa.accept_17_4_10_15_1_5444 21 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 146 236 2 10 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 146 236 (accept_3_2 19 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 236 2 9 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 236 2 8 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 236 2 7 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 236 (accept_3_2 13 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 236 2 6 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 146 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 236 2 5 73 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 236
  (Polychromatic418967fa.accept_13_9_3_2_1_399 9 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 236 2 4 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 236 (accept_3_2 7 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  236 2 3 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 146 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 236 2 2 73 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 236 (Polychromatic418967fa.accept_19_3_13_8_1_4476 3 146 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 236 2 1 73 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 236 (accept_3_2 1 146 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 145 236
  (Eq.refl Bool.true) (allA_of_3_0 92 145 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 144 236 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 144 236 4 23 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 144 236 (accept_3_2 91 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 236 2 45 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 236 (Polychromatic418967fa.accept_22_1_12_16_1_6178 89 144 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 236 4 22 36 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 236
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 87 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 144 236 2 43 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 144 236 (accept_3_2 85 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 236 4 21 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 236 2 41 72 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 236
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 81 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 236 4 20 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 144 236 (accept_3_2 79 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 144 236 2 39 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 144 236 (Polychromatic418967fa.accept_13_12_1_2_1_845 77 144 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 236 4 19 36 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 75 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 144 236 2 37 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 236 (accept_3_2 73 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 236 4 18 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 236 2 35 72 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 144 236 4 17 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 236 (accept_3_2 67 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 236 2 33 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 236 4 16 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 236
  (Polychromatic418967fa.accept_22_19_12_16_1_6241 63 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 144 236 2 31 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 144 236 (accept_3_2 61 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 236 4 15 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 236 (Polychromatic418967fa.accept_19_2_11_8_1_2090 59 144 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 236 2 29 72 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 236 4 14 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 236 (accept_3_2 55 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 236 2 27 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 236 (Polychromatic418967fa.accept_21_11_18_5_1_8162 53 144 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 236 4 13 36 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 144 236 2 25 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 236 (accept_3_2 49 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 236 4 12 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 236 (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 144 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 236 2 23 72 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 236
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 236 4 11 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 236 (accept_3_2 43 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 236 2 21 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 236 4 10 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 236
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 236 2 19 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 236 (accept_3_2 37 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 236 4 9 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 144 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 236 2 17 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 236
  (Polychromatic418967fa.accept_21_12_18_5_1_14149 33 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 144 236 4 8 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 144 236 (accept_3_2 31 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 236 2 15 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 236 4 7 36 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 236 2 13 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 236 (accept_3_2 25 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 236 4 6 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 144 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 236 2 11 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 236 (Polychromatic418967fa.accept_15_6_9_11_1_858
  21 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 236 4 5 36 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 236
  (accept_3_2 19 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 236 2 9 72 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 236
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 236 4 4 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 144 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 236 2 7 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 236 (accept_3_2 13 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 236 4 3 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 236 (Polychromatic418967fa.accept_21_11_18_5_1_8162 11 144
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 236 2 5 72 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 236 4 2 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 236 (accept_3_2 7 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  236 2 3 72 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 144 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 236 4 1 36 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 236 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 144 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 236 2 1 72 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 236 (accept_3_2 1 144 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 143
  236 (Eq.refl Bool.true) (allA_succ_of_accept 93 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 92 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 143 236 (accept_3_2 91 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 143 236 (Polychromatic418967fa.accept_17_5_7_15_1_1230 90 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 143 236 (Polychromatic418967fa.accept_10_9_3_6_1_686 89 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 143 236 (accept_3_2 88 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 143 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 86 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 143 236 (accept_3_2 85 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 143 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 143 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 83 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 143 236 (accept_3_2 82 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 236
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 80 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 143 236 (accept_3_2 79 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 143 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 143 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 236 (accept_3_2 76 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 236 (accept_3_2 73 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 236 (accept_3_2 70 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 236 (accept_3_2 67 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 236 (accept_3_2 64 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 236
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 236 (accept_3_2 61 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 236 (accept_3_2 58 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 236
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 143 236 (accept_3_2 55 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 143 236 (Polychromatic418967fa.accept_19_16_10_8_1_10067 54 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 236
  (Polychromatic418967fa.accept_17_2_7_15_1_5525 53 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 236 (accept_3_2 52 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 236 (accept_3_2 49 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 236
  (Polychromatic418967fa.accept_10_7_3_6_1_644 47 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 236 (accept_3_2 46 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 236 (accept_3_2 43 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 236 (accept_3_2 40 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 236 (accept_3_2 37 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 143 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 236 (accept_3_2 34 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 236 (accept_3_2 31 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 236
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 236 (accept_3_2 28 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 236 (accept_3_2 25 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 236
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 236 (accept_3_2 22 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 236 (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 236 (accept_3_2 19 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 236 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 143
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 236
  (Polychromatic418967fa.accept_10_7_3_6_1_644 17 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 236 (accept_3_2 16 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 236 (accept_3_2 13 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 236
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 236 (accept_3_2 10 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 236 (accept_3_2 7 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 236 (accept_3_2 4 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 236 (accept_3_2 1 143 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 142
  236 (Eq.refl Bool.true) (allA_of_3_0 95 142 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 141 236
  (Eq.refl Bool.true) (allA_succ_of_accept 95 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 141 236 (accept_3_2 94 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 141 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 141 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 141 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 92 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 141 236 (accept_3_2 91 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 141 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 90 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 141 236 (accept_3_2 88 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 141 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 87 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 141 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 86 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 141 236 (accept_3_2 85 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 141 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 141 236 (accept_3_2 82 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 141 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 81 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 80 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 141 236 (accept_3_2 79 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 141 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 236 (accept_3_2 76 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 236 (accept_3_2 73 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 141 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 236 (accept_3_2 70 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 141 236 (accept_3_2 67 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 141 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 236 (accept_3_2 64 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 236 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 141 236 (accept_3_2 61 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 141 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 236 (accept_3_2 58 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 236
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 56 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 236 (accept_3_2 55 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 141 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 236 (accept_3_2 52 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 236 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 236 (accept_3_2 49 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 141 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 236 (accept_3_2 46 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 236 (accept_3_2 43 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 141 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 236 (accept_3_2 40 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 236 (accept_3_2 37 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 236 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 236 (accept_3_2 34 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 236 (accept_3_2 31 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 236 (accept_3_2 28 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 236 (accept_3_2 25 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 236 (accept_3_2 22 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 236 (accept_3_2 19 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 236 (accept_3_2 16 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 236 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 236
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 236 (accept_3_2 13 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 236 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 236 (accept_3_2 10 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 236
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 236 (accept_3_2 7 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 236 (accept_3_2 4 141 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 236
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 236 (accept_3_2 1 141 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 140
  236 (Eq.refl Bool.true) (allA_succ_of_gcd 96 140 236 4 24 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 140 236 (Polychromatic418967fa.accept_17_10_4_15_1_2165 95 140
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 236 2 47 70 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 236 4 23 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 236 (accept_3_2 91 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 236 2 45 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 140 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 236 4 22 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 236 2 43 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 140 236 (accept_3_2 85 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 236 4 21 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 83 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 236 2 41 70 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 236
  (Polychromatic418967fa.accept_13_3_10_2_1_381 81 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 236 4 20 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 236 (accept_3_2 79 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 236 2 39 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 236 (Polychromatic418967fa.accept_13_12_10_2_1_1451 77 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 236 4 19 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 236 2 37 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 236 (accept_3_2 73 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 236 4 18 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 140 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 236 2 35 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 236 4 17 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 236 (accept_3_2 67 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 236 2 33 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 236 (Polychromatic418967fa.accept_18_11_14_2_1_5058 65 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 236 4 16 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 236
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 140 236 2 31 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 140 236 (accept_3_2 61 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 236 4 15 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 236 (Polychromatic418967fa.accept_21_17_14_5_1_9767 59 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 236 2 29 70 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 236 4 14 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 236 (accept_3_2 55 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 236 2 27 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 140 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 236 4 13 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 236
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 236 2 25 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 236 (accept_3_2 49 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 236 4 12 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 47 140 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 236 2 23 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 236
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 236 4 11 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 236 (accept_3_2 43 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 236 2 21 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 236 (Polychromatic418967fa.accept_21_20_14_5_1_8194 41 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 236 4 10 35 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 236 2 19 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 236 (accept_3_2 37 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 236 4 9 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 140 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 140 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 236 2 17 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 33
  140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 236 4 8 35 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 236 (accept_3_2 31
  140 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 236 2 15 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 236
  (Polychromatic418967fa.accept_13_3_10_2_1_381 29 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 236 4 7 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 236 (Polychromatic418967fa.accept_17_10_4_15_1_2165 27 140 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 236 2 13 70 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 236 (accept_3_2 25 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 236 4 6 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 236 (Polychromatic418967fa.accept_15_8_5_11_1_2358
  23 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 236 2 11 70 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 236 4 5 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 236 (accept_3_2 19 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 236 2 9 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 236 4 4 35 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 236 2 7 70 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 236 (accept_3_2 13
  140 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 236 4 3 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 236
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 236 2 5 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 236 (Polychromatic418967fa.accept_15_9_5_11_1_5416 9 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 236 4 2 35 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 236 (accept_3_2 7 140 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 236 2 3 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 236 (Polychromatic418967fa.accept_13_5_10_2_1_856 5
  140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 236 4 1 35 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 236
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 236 2 1 70 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 236 (accept_3_2 1 140 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  139 236 (Eq.refl Bool.true) (allA_of_3_0 98 139 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 138 236
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 138 236 2 49 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 138 236 (accept_3_2 97 138 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 138 236 2 48 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 138 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 95 138 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 236 2 47 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 93 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 138 236 2 46 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 236 (accept_3_2 91 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 236 2 45 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 236 2 44 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 87 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 236 2 43 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 236 (accept_3_2 85 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 236 2 42 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 83 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 236 2 41 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 236 2 40 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 236 (accept_3_2 79 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 236 2 39 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 236 2 38 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 236 2 37 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 236 (accept_3_2 73 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 236 2 36 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 236 2 35 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 236 2 34 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 236 (accept_3_2 67 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 236 2 33 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 236 (Polychromatic418967fa.accept_11_10_6_5_1_1239 65 138 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 236 2 32 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 236 2 31 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 236 (accept_3_2 61 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 236 2 30 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 236 2 29 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 236 2 28 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 236 (accept_3_2 55 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 236 2 27 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 236 2 26 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 236 2 25 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 236 (accept_3_2 49 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 236 2 24 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 236 (Polychromatic418967fa.accept_17_13_2_15_1_2151 47 138 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 236 2 23 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 236
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 236 2 22 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 236 (accept_3_2 43 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 236 2 21 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 236 2 20 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 236 2 19 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 236 (accept_3_2 37 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 236 2 18 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 236 2 17 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 236 2 16 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 236 (accept_3_2 31 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 236 2 15 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 236 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 138 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 236 2 14 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 236 2 13 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 236 (accept_3_2 25 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 236 2 12 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 236 2 11 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 236
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 236 2 10 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 236 (accept_3_2 19 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 236 2 9 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 138 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 236 2 8 69 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 236
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 236 2 7 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 236 (accept_3_2 13 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 236 2 6 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 236 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 138 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 236 2 5 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 236 2 4 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 236 (accept_3_2 7 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  236 2 3 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 236 2 2 69 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 236 2 1 69 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 236 (accept_3_2 1 138 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  137 236 (Eq.refl Bool.true) (allA_succ_of_accept 99 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 137 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 137 236 (accept_3_2 97 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 137 236 (Polychromatic418967fa.accept_13_5_7_2_1_852 96 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 137 236 (Polychromatic418967fa.accept_15_5_2_11_1_1596 95 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 137 236 (accept_3_2 94 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 137 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 92 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 137 236 (accept_3_2 91 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 137 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 90 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 137 236 (Polychromatic418967fa.accept_18_17_11_2_1_7782 89 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 137 236 (accept_3_2 88 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 137 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 86 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 137 236 (accept_3_2 85 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 137 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 84 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 137 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 137 236 (accept_3_2 82 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 236
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 80 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 137 236 (accept_3_2 79 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 137 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 78 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 137 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 236 (accept_3_2 76 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 236 (accept_3_2 73 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 236 (accept_3_2 70 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 236
  (Polychromatic418967fa.accept_16_4_9_12_1_4829 68 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 236 (accept_3_2 67 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 236 (Polychromatic418967fa.accept_15_6_2_11_1_325 66 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 236 (accept_3_2 64 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 236 (accept_3_2 61 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 60 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 236 (Polychromatic418967fa.accept_20_19_17_16_1_2732 59 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 236 (accept_3_2 58 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 236
  (Polychromatic418967fa.accept_16_8_9_12_1_1737 56 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 236 (accept_3_2 55 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 236 (accept_3_2 52 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 236 (accept_3_2 49 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 236 (Polychromatic418967fa.accept_13_8_7_2_1_2988 47 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 236 (accept_3_2 46 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 236 (accept_3_2 43 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 236 (Polychromatic418967fa.accept_22_20_5_16_1_14148 42 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 236 (accept_3_2 40 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 236 (accept_3_2 37 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 236 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 236 (accept_3_2 34 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 236
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 32 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 137 236 (accept_3_2 31 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 137 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 137 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 236 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 236 (accept_3_2 28 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 236 (accept_3_2 25 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 236 (Polychromatic418967fa.accept_15_9_2_11_1_2391 24 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 236 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 236 (accept_3_2 22 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 236
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 236 (accept_3_2 19 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 236 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 236 (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 236 (accept_3_2 16 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 236 (accept_3_2 13 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 236 (Polychromatic418967fa.accept_17_12_1_15_1_5472 12 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 236 (Polychromatic418967fa.accept_10_1_7_6_1_91 11 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 236 (accept_3_2 10 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 236
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 236 (accept_3_2 7 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 236 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 236 (accept_3_2 4 137 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 236
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 236 (accept_3_2 1 137 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 136 236 (Eq.refl Bool.true) (allA_of_3_0 101 136 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 135
  236 (Eq.refl Bool.true) (allA_succ_of_accept 101 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 135 236 (accept_3_2 100 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 135 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 99
  135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 236
  (Polychromatic418967fa.accept_13_7_5_2_1_401 98 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 135 236 (accept_3_2 97 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 135 236 (Polychromatic418967fa.accept_11_8_3_5_1_355 96 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 236 (accept_3_2 94 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 236 (Polychromatic418967fa.accept_18_3_9_2_1_5053 93 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 236
  (Polychromatic418967fa.accept_25_17_10_11_1_14147 92 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 135 236 (accept_3_2 91 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 135 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 135 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 236 (accept_3_2 88 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 236 (Polychromatic418967fa.accept_7_3_2_5_1_147
  87 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 236
  (Polychromatic418967fa.accept_17_1_16_15_1_4315 86 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 135 236 (accept_3_2 85 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 135 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 84 135 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 236 (accept_3_2 82 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 236 (Polychromatic418967fa.accept_7_4_2_5_1_527
  81 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 135 236 (accept_3_2 79 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 135 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 236 (accept_3_2 76 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 236 (accept_3_2 73 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 135 236 (Polychromatic418967fa.accept_13_7_5_2_1_401 72 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 236 (accept_3_2 70 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 69 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 236
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 68 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 236 (accept_3_2 67 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 135 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 236 (accept_3_2 64 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 236 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 236
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 62 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 236 (accept_3_2 61 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 135 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 236 (accept_3_2 58 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 236 (Polychromatic418967fa.accept_18_3_9_2_1_5053 57 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 236
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 56 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 236 (accept_3_2 55 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 236 (accept_3_2 52 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 236
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 50 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 236 (accept_3_2 49 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 236 (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 236 (accept_3_2 46 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 236 (accept_3_2 43 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 236 (accept_3_2 40 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 236 (accept_3_2 37 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 236 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 236 (accept_3_2 34 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 236 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 236 (accept_3_2 31 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 236 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 236 (accept_3_2 28 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 236 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 236
  (Polychromatic418967fa.accept_23_3_20_6_1_14146 26 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 135 236 (accept_3_2 25 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 135 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 135 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 236 (accept_3_2 22 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 236 (Polychromatic418967fa.accept_10_1_5_6_1_649
  21 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 236
  (Polychromatic418967fa.accept_13_7_5_2_1_401 20 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 236 (accept_3_2 19 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 236 (accept_3_2 16 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 236 (Polychromatic418967fa.accept_19_15_2_8_1_7263 15 135 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 236 (accept_3_2 13 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 236 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 236 (accept_3_2 10 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 236 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 236
  (Polychromatic418967fa.accept_11_8_3_5_1_355 8 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 236 (accept_3_2 7 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 236 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 236 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 236 (accept_3_2 4 135 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 236
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 2 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 236 (accept_3_2 1 135 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 134 236 (Eq.refl Bool.true) (allA_succ_of_gcd 102 134 236 2 51 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 134 236 (Polychromatic418967fa.accept_7_3_1_5_1_44
  101 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 134 236 2 50 67 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 134 236
  (Polychromatic418967fa.accept_21_15_8_5_1_12668 99 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 134 236 2 49 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 134 236 (accept_3_2 97 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 134 236 2 48 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 134 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 95 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 236 2 47 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 93 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 236 2 46 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 236 (accept_3_2 91 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 236 2 45 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 236 2 44 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 87 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 236 2 43 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 236 (accept_3_2 85 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 236 2 42 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 83 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 236 2 41 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 81 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 236 2 40 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 236 (accept_3_2 79 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 236 2 39 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 236 2 38 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 236 2 37 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 236 (accept_3_2 73 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 236 2 36 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 134 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 236 2 35 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 236 2 34 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 236 (accept_3_2 67 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 236 2 33 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 65 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 236 2 32 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 236
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 236 2 31 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 236 (accept_3_2 61 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 236 2 30 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 236 2 29 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 236 2 28 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 236 (accept_3_2 55 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 236 2 27 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 236 2 26 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 236 2 25 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 236 (accept_3_2 49 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 236 2 24 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 236 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 134 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 236 2 23 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 236
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 236 2 22 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 236 (accept_3_2 43 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 236 2 21 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 236 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 236 2 20 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 236
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 236 2 19 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 236 (accept_3_2 37 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 236 2 18 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 236 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 236 2 17 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 236 2 16 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 236 (accept_3_2 31 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 236 2 15 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 236 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 236 2 14 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 236
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 236 2 13 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 236 (accept_3_2 25 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 236 2 12 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 236 2 11 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 236 2 10 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 236 (accept_3_2 19 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 236 2 9 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 236 2 8 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 236 2 7 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 236 (accept_3_2 13 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 236 2 6 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 236 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 134 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 236 2 5 67 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 236
  (Polychromatic418967fa.accept_19_9_1_8_1_12907 9 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 236 2 4 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 236 (accept_3_2 7 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  236 2 3 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 134 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 236 2 2 67 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 236 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 134 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 236 2 1 67 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 236 (accept_3_2 1 134 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 133 236 (Eq.refl Bool.true) (allA_of_3_0 104 133 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 132
  236 (Eq.refl Bool.true) (allA_succ_of_gcd 104 132 236 4 26 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 236 (accept_3_2 103 132 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 132 236 2 51 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 132 236 (Polychromatic418967fa.accept_10_1_2_6_1_638 101 132 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 132 236 4 25 33 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 132 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 99 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 132 236 2 49 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 132 236 (accept_3_2 97 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 132 236 4 24 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 132 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 132 236 2 47 66 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 132 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 132 236 4 23 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 132 236 (accept_3_2 91 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 132 236 2 45 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 236 4 22 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 236
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 87 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 132 236 2 43 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 132 236 (accept_3_2 85 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 236 4 21 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 236 (Polychromatic418967fa.accept_14_13_6_12_1_3126 83 132 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 236 2 41 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 236 4 20 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 236 (accept_3_2 79 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 236 2 39 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 236 4 19 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 236 2 37 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 236 (accept_3_2 73 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 236 4 18 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 236 2 35 66 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 236
  (Polychromatic418967fa.accept_14_13_6_12_1_3126 69 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 132 236 4 17 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 132 236 (accept_3_2 67 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 236 2 33 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 236 (Polychromatic418967fa.accept_16_1_4_12_1_376 65 132 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 236 4 16 33 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 236
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 132 236 2 31 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 132 236 (accept_3_2 61 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 236 4 15 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 236 2 29 66 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 236 4 14 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 236 (accept_3_2 55 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 236 2 27 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 236 4 13 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 236
  (Polychromatic418967fa.accept_10_1_2_6_1_638 51 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 236 2 25 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 236 (accept_3_2 49 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 236 4 12 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 236 (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 132 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 236 2 23 66 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 236
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 132 236 4 11 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 132 236 (accept_3_2 43 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 236 2 21 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 236 4 10 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 236 2 19 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 236 (accept_3_2 37 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 236 4 9 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 236 2 17 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 236 (Polychromatic418967fa.accept_16_1_4_12_1_376
  33 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 236 4 8 33 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 236
  (accept_3_2 31 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 236 2 15 66 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 236 4 7 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 236 (Polychromatic418967fa.accept_14_13_6_12_1_3126 27 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 236 2 13 66 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 236 (accept_3_2 25 132 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 236 4 6 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 236 2 11 66 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 236 4 5 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 236 (accept_3_2 19 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  132 236 2 9 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 236 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 236 4 4 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 236 2 7 66 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 236 (accept_3_2 13
  132 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 236 4 3 33 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 236 2 5 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 132 236 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 236 4 2 33 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 236 (accept_3_2 7 132 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 236 2 3 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 236 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 236 4 1 33 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 236
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 236 2 1 66 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 236 (accept_3_2 1 132 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 131 236 (Eq.refl Bool.true) (allA_succ_of_accept 105 131 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 131 236 (Polychromatic418967fa.accept_16_8_3_12_1_1819 104 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 131 236 (accept_3_2 103 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 102 131 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 236
  (Polychromatic418967fa.accept_14_3_5_12_1_4000 101 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 131 236 (accept_3_2 100 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 236 (accept_3_2 97 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 236 (Polychromatic418967fa.accept_9_6_5_2_1_421
  96 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 95 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 236 (accept_3_2 94 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 92 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 236 (accept_3_2 91 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 236 (Polychromatic418967fa.accept_13_12_1_2_1_845 90 131
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 236 (accept_3_2 88 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 236 (accept_3_2 85 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 236
  (Polychromatic418967fa.accept_11_6_10_5_1_341 83 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 236 (accept_3_2 82 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 236 (accept_3_2 79 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 236
  (Polychromatic418967fa.accept_10_7_1_6_1_673 77 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 236 (accept_3_2 76 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 74 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 236 (accept_3_2 73 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 72 131
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 71 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 236 (accept_3_2 70 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 236 (Polychromatic418967fa.accept_13_3_1_2_1_2960 68 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 236 (accept_3_2 67 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 236
  (Polychromatic418967fa.accept_10_5_1_6_1_672 65 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 236 (accept_3_2 64 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 236 (accept_3_2 61 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 236
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 236 (accept_3_2 58 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 236 (Polychromatic418967fa.accept_16_8_3_12_1_1819 56 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 236 (accept_3_2 55 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 236 (Polychromatic418967fa.accept_17_3_12_15_1_1203 54 131
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 236 (accept_3_2 52 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 236 (Polychromatic418967fa.accept_11_6_10_5_1_341 50 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 236 (accept_3_2 49 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 236 (accept_3_2 46 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 236 (accept_3_2 43 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 236
  (Polychromatic418967fa.accept_16_9_3_12_1_1802 41 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 236 (accept_3_2 40 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 236 (accept_3_2 37 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 236 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 131
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 236 (accept_3_2 34 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 236 (accept_3_2 31 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 236
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 236 (accept_3_2 28 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 236 (accept_3_2 25 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 236
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 236 (accept_3_2 22 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 236 (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 236 (accept_3_2 19 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 236 (Polychromatic418967fa.accept_17_1_12_15_1_1263 18 131
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 236
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 236 (accept_3_2 16 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 236 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 236 (accept_3_2 13 131 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 236 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 236
  (Polychromatic418967fa.accept_19_11_17_8_1_7259 11 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 131 236 (accept_3_2 10 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 236 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 236 (accept_3_2 7 131 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 236 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 236
  (Polychromatic418967fa.accept_10_5_1_6_1_672 5 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 236 (accept_3_2 4 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 236 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 236 (accept_3_2 1 131 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 130 236 (Eq.refl Bool.true) (allA_of_3_0 107 130 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 129 236 (Eq.refl Bool.true) (allA_succ_of_accept 107 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 236 (accept_3_2 106 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 129 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 236 (accept_3_2 103 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 236 (Polychromatic418967fa.accept_11_3_8_5_1_336 102 129
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 129 236 (accept_3_2 100 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 99 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 129 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 236 (accept_3_2 97 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 236 (accept_3_2 94 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 93 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 92 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 236 (accept_3_2 91 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 236 (Polychromatic418967fa.accept_11_2_8_5_1_1219 90 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 236 (accept_3_2 88 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 86 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 236 (accept_3_2 85 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 236 (Polychromatic418967fa.accept_13_6_12_2_1_4707 84 129 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 236 (accept_3_2 82 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 236 (Polychromatic418967fa.accept_13_3_12_2_1_385 81 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 236 (accept_3_2 79 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 236 (accept_3_2 76 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 236 (Polychromatic418967fa.accept_10_5_9_6_1_697 75 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 236 (Polychromatic418967fa.accept_19_17_15_8_1_5936 74 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 236 (accept_3_2 73 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 129 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 236 (accept_3_2 70 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 236 (accept_3_2 67 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 236 (accept_3_2 64 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 236 (accept_3_2 61 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 236 (accept_3_2 58 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 236 (Polychromatic418967fa.accept_13_4_12_2_1_1459 56 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 236 (accept_3_2 55 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 129
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 236 (accept_3_2 52 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 236 (accept_3_2 49 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 236 (accept_3_2 46 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 236 (accept_3_2 43 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 236 (accept_3_2 40 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 236 (Polychromatic418967fa.accept_17_5_10_15_1_5574 39 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 236 (Polychromatic418967fa.accept_17_4_10_15_1_5444 38 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 236 (accept_3_2 37 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 129 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 236 (accept_3_2 34 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 236 (accept_3_2 31 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 236 (accept_3_2 28 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 236 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 236 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 236 (accept_3_2 25 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 236 (accept_3_2 22 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 236 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 236 (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 236 (accept_3_2 19 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 236 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 129
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 236 (accept_3_2 16 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 236 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 236 (accept_3_2 13 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 236 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 236 (accept_3_2 10 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 236 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 236 (accept_3_2 7 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 236 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 236
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 236 (accept_3_2 4 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 236 (Polychromatic418967fa.accept_10_3_9_6_1_94 3 129 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 236 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 236 (accept_3_2 1 129 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 128 236 (Eq.refl Bool.true) (allA_succ_of_gcd 108 128 236 4 27 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 128 236
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 107 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 128 236 2 53 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 128 236 (Polychromatic418967fa.accept_14_7_2_12_1_1430 105 128 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 128 236 4 26 32 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 128 236 (accept_3_2
  103 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 128 236 2 51 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 128 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 101 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 128 236 4 25 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 128 236 (Polychromatic418967fa.accept_19_4_14_8_1_4510 99 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 128 236 2 49 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 128 236 (accept_3_2 97 128 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 128 236 4 24 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 128 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 95 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 128 236 2 47 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 128 236 (Polychromatic418967fa.accept_10_3_8_6_1_326 93 128 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 128 236 4 23 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 128 236 (accept_3_2 91 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 128 236 2 45 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 128 236
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 89 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 128 236 4 22 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 128 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 87 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 128 236 2 43 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 128 236 (accept_3_2 85 128 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 128 236 4 21 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 128 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 83 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 128 236 2 41 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 128 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 81 128 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 128 236 4 20 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 128 236 (accept_3_2 79 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 128 236 2 39 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 128 236 (Polychromatic418967fa.accept_14_7_2_12_1_1430
  77 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 236 4 19 32 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 236
  (Polychromatic418967fa.accept_11_9_7_5_1_749 75 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 236 2 37 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 236 (accept_3_2 73 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 236 4 18 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 236 (Polychromatic418967fa.accept_21_8_2_5_1_8163 71 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 236 2 35 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 236
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 69 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 236 4 17 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 236 (accept_3_2 67 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 236 2 33 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 236 (Polychromatic418967fa.accept_15_5_8_11_1_2350 65 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 236 4 16 32 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 236
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 128 236 2 31 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 128 236 (accept_3_2 61 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 236 4 15 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 128 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 236 2 29 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 236
  (Polychromatic418967fa.accept_15_12_8_11_1_4383 57 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 128 236 4 14 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 128 236 (accept_3_2 55 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 236 2 27 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 128 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 236 4 13 32 59 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 236
  (Polychromatic418967fa.accept_19_13_14_8_1_4490 51 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 128 236 2 25 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 128 236 (accept_3_2 49 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 236 4 12 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 236 (Polychromatic418967fa.accept_19_9_14_8_1_11549 47 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 236 2 23 64 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 236
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 236 4 11 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 236 (accept_3_2 43 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 236 2 21 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 236 (Polychromatic418967fa.accept_17_7_9_15_1_8105 41 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 236 4 10 32 59 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 236
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 236 2 19 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 236 (accept_3_2 37 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 236 4 9 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 236 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 128 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 236 2 17 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 236 (Polychromatic418967fa.accept_10_3_8_6_1_326
  33 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 236 4 8 32 59
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 236
  (accept_3_2 31 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 236 2 15 64 118 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 236
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 236 4 7 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 236 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 128 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 236 2 13 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 236 (accept_3_2 25 128 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 236 4 6 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 236 (Polychromatic418967fa.accept_10_3_8_6_1_326
  23 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 236 2 11 64 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 236
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 21 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 236 4 5 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 236 (accept_3_2 19 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 236 2 9 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 128 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 236 4 4 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 236
  (Polychromatic418967fa.accept_24_15_8_20_1_12559 15 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 128 236 2 7 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 128 236 (accept_3_2 13 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 236 4 3 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 128 236 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 128 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 236 2 5 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 236 (Polychromatic418967fa.accept_11_9_7_5_1_749 9
  128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 236 4 2 32 59 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 236 (accept_3_2 7
  128 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 236 2 3 64 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 236
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 128 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 128 236 4 1 32 59 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 128 236 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 128 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 236 2 1 64 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 236 (accept_3_2 1 128 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 127 236 (Eq.refl Bool.true) (allA_of_3_0 110 127 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 126 236 (Eq.refl Bool.true) (allA_succ_of_gcd 110 126 236 2 55 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 126 236 (accept_3_2 109 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 126 236 2 54 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 126 236 (Polychromatic418967fa.accept_13_3_9_2_1_1486
  107 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 236 2 53 63 118
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 105 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 126 236 2 52 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 126 236 (accept_3_2 103 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 126 236 2 51 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 126 236 (Polychromatic418967fa.accept_19_6_12_8_1_8798 101 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 236 2 50 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 236 2 49 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 236 (accept_3_2 97 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 236 2 48 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 95 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 236 2 47 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 236 2 46 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 236 (accept_3_2 91 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 236 2 45 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 236 (Polychromatic418967fa.accept_13_11_9_2_1_2969 89 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 236 2 44 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 236 2 43 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 236 (accept_3_2 85 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 236 2 42 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 236 (Polychromatic418967fa.accept_13_5_9_2_1_1489 83 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 236 2 41 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 236 2 40 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 236 (accept_3_2 79 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 236 2 39 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 236 (Polychromatic418967fa.accept_15_2_6_11_1_1587 77 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 236 2 38 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 236 2 37 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 236 (accept_3_2 73 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 236 2 36 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 236 (Polychromatic418967fa.accept_13_6_9_2_1_838 71 126 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 236 2 35 63 118 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 236 2 34 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 236 (accept_3_2 67 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 236 2 33 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 65 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 236 2 32 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 236 2 31 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 236 (accept_3_2 61 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 236 2 30 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 236 (Polychromatic418967fa.accept_13_7_9_2_1_2167 59 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 236 2 29 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 236 2 28 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 236 (accept_3_2 55 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 236 2 27 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 236 (Polychromatic418967fa.accept_13_1_9_2_1_1448 53 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 236 2 26 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 236 2 25 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 236 (accept_3_2 49 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 236 2 24 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 236 (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 236 2 23 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 236 2 22 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 236 (accept_3_2 43 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 236 2 21 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 236 (Polychromatic418967fa.accept_20_1_6_16_1_6991 41 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 236 2 20 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 236 2 19 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 236 (accept_3_2 37 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 236 2 18 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 236 (Polychromatic418967fa.accept_15_5_6_11_1_854 35 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 236 2 17 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 236 2 16 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 236 (accept_3_2 31 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 236 2 15 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 236 (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 236 2 14 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 236 2 13 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 236 (accept_3_2 25 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 236 2 12 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 236 (Polychromatic418967fa.accept_19_4_12_8_1_10123 23 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 236 2 11 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 236 2 10 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 236 (accept_3_2 19 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 236 2 9 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 236 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 236 2 8 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 236
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 236 2 7 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 236 (accept_3_2 13 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 236 2 6 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 236 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 236 2 5 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 236
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 236 2 4 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 236 (accept_3_2 7 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  236 2 3 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 236 (Polychromatic418967fa.accept_13_5_9_2_1_1489 5 126 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 236 2 2 63 118 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 236 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 126 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 236 2 1 63 118 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 236 (accept_3_2 1 126 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  236)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 125 236 (Eq.refl Bool.true) (allA_succ_of_accept 111 125 236
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 125 236 (Polychromatic418967fa.accept_12_2_5_8_1_159 110 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 125 236 (accept_3_2 109 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 125 236 (Polychromatic418967fa.accept_23_16_10_6_1_14145 108 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 125 236
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 107 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 125 236 (accept_3_2 106 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 125
  236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 125 236 (accept_3_2 103 125
  236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 125 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 102 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 125 236 (Polychromatic418967fa.accept_10_1_5_6_1_649 101 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 236 (accept_3_2 100 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 236 (Polychromatic418967fa.accept_11_10_4_5_1_359
  98 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 236 (accept_3_2 97
  125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 125 236
  (Polychromatic418967fa.accept_9_6_8_2_1_410 96 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 125 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 95 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 125 236 (accept_3_2 94 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 92
  125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 236 (accept_3_2 91
  125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 236
  (Polychromatic418967fa.accept_14_6_13_12_1_810 90 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 125 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 89 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 236 (accept_3_2 88 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 236 (Polychromatic418967fa.accept_9_5_8_2_1_409
  86 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 236 (accept_3_2 85
  125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 236
  (Polychromatic418967fa.accept_9_3_8_2_1_162 84 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 125 236 (Polychromatic418967fa.accept_15_8_5_11_1_2358 83 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 236 (accept_3_2 82 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 236
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 80 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 125 236 (accept_3_2 79 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 125 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 125 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 236 (accept_3_2 76 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 125 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 74 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 236 (accept_3_2 73 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 236 (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 236 (accept_3_2 70 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 236 (accept_3_2 67 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 236 (accept_3_2 64 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 236 (accept_3_2 61 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 236 (accept_3_2 58 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 236
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 56 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 125 236 (accept_3_2 55 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 125 236 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 125 236 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 125 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 236 (accept_3_2 52 125 236
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 236 (accept_3_2 49 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 236 (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 236 (accept_3_2 46 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 236
  (Polychromatic418967fa.accept_10_4_5_6_1_651 44 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 236 (accept_3_2 43 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 236 (accept_3_2 40 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 236 (accept_3_2 37 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 236 (Polychromatic418967fa.accept_19_16_11_8_1_8758 35 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 236 (accept_3_2 34 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 236
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 236
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 236 (accept_3_2 31 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 236 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 236 (accept_3_2 28 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 236 (accept_3_2 25 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 236 (accept_3_2 22 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 236
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 236 (accept_3_2 19 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 236 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 236 (accept_3_2 16 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 236
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 236 (accept_3_2 13 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 236 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 236 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 236 (accept_3_2 10 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 236
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 236 (accept_3_2 7 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 236 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 236 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 236 (accept_3_2 4 125 236 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 236 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 236 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 236
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 236 (accept_3_2 1 125 236 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  236))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_236_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


