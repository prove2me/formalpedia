-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch128
-- name    : Polychromatic418967fa_Branch128
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:12:39.826318+00:00
-- url     : https://prove2.me/theorems/0c6fdc32-cfa4-4d1f-ad2a-6062fc090017
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_128 : allB 128 128 :=
  allB_succ' 2 127 128 (Eq.refl Bool.true) (allA_of_3_0 2 127 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  126 128 (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 128 2 1 63 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 128 (accept_3_2 1 126 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126 128))) (allB_succ' 4 125 128 (Eq.refl Bool.true) (allA_succ_of_accept 3 125 128
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 125 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 125 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 128 (accept_3_2 1 125 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 125 128)))) (allB_succ' 5 124 128 (Eq.refl Bool.true) (allA_of_3_0 5 124 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 123 128 (Eq.refl Bool.true) (allA_succ_of_accept 5 123 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 128 (accept_3_2 4 123 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 128 (Polychromatic418967fa.accept_17_2_4_9_1_2791 2 123 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 128 (accept_3_2 1 123 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 128)))))) (allB_succ' 7 122 128 (Eq.refl Bool.true) (allA_succ_of_gcd 6 122 128 2 3
  61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 128
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 122 128 2 2 61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 122 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 122 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 128 2 1 61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 128 (accept_3_2 1 122 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 122 128))))))) (allB_succ' 8 121 128 (Eq.refl Bool.true) (allA_of_3_0 8 121 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 120 128 (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 128 8 1 15 16
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 128
  (accept_3_2 7 120 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 128 2 3 60 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 120 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 120 128 4 1 30 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 120 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 120 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 128 2 1 60 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 128 (accept_3_2 1 120 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 128))))))))) (allB_succ' 10 119 128 (Eq.refl Bool.true) (allA_succ_of_accept 9 119 128
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 119 128 (Polychromatic418967fa.accept_19_8_5_14_1_3586 8 119 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 128 (accept_3_2 7 119 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 119 128 (Polychromatic418967fa.accept_15_6_14_8_1_245 6 119 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 128 (Polychromatic418967fa.accept_11_5_9_7_1_411 5
  119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 128 (accept_3_2 4 119
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 128 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 128
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 128 (accept_3_2 1 119 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  128)))))))))) (allB_succ' 11 118 128 (Eq.refl Bool.true) (allA_of_3_0 11 118 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 117 128 (Eq.refl Bool.true) (allA_succ_of_accept 11 117 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 128 (accept_3_2 10 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 128 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 128 (Polychromatic418967fa.accept_19_8_3_14_1_3571 8 117 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 128 (accept_3_2 7 117 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 128 (accept_3_2 4 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 117 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 128 (Polychromatic418967fa.accept_22_2_7_18_1_6403 2 117 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 128 (accept_3_2 1 117 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 128)))))))))))) (allB_succ' 13 116 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 116 128 4 3 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 116 128 (Polychromatic418967fa.accept_22_11_6_18_1_6402 11 116 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 116 128 2 5 58 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 116 128
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 116 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 116 128 4 2 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 116 128 (accept_3_2 7 116 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116
  128 2 3 58 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  116 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 116 128 4 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 116 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 116 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 128 2 1 58 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 128 (accept_3_2 1 116 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 128))))))))))))) (allB_succ' 14 115 128 (Eq.refl Bool.true) (allA_of_3_0 14 115 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 114 128 (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 128 2 7
  57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 128
  (accept_3_2 13 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 128 2 6 57 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 128
  (Polychromatic418967fa.accept_21_11_9_2_1_6354 11 114 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 128 2 5 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 128 2 4 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 128 (accept_3_2 7 114 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 128 2 3 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 128 2 2 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  114 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 128 2 1 57 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 128 (accept_3_2 1
  114 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 128))))))))))))))) (allB_succ' 16 113 128 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 113 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 128 (Polychromatic418967fa.accept_12_2_5_8_1_159
  14 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 128 (accept_3_2 13
  113 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 128
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 113 128 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 128 (accept_3_2 10 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 113 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 128 (accept_3_2 7 113
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 128
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 113 128 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 128 (accept_3_2 4 113 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 113 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  113 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 128 (accept_3_2 1 113
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113 128)))))))))))))))) (allB_succ' 17 112 128 (Eq.refl
  Bool.true) (allA_of_3_0 17 112 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 111 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 111 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 128 (accept_3_2 16 111 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 111 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 128 (Polychromatic418967fa.accept_9_5_3_2_1_171
  14 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 128 (accept_3_2 13
  111 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 128
  (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 128 (accept_3_2 10 111 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 128 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 111 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 128 (accept_3_2 7 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 128 (accept_3_2 4 111 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 111 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 128
  (Polychromatic418967fa.accept_15_2_6_8_1_754 2 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 128 (accept_3_2 1 111 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  128)))))))))))))))))) (allB_succ' 19 110 128 (Eq.refl Bool.true) (allA_succ_of_gcd 18 110 128 2 9 55 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 110 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 110 128 2 8 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 110 128 (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 110 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 128 2 7 55 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 128 (accept_3_2 13 110 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 128 2 6 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 11
  110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 128 2 5 55 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 128
  (Polychromatic418967fa.accept_24_9_14_8_1_6401 9 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 128 2 4 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 128 (accept_3_2 7 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  128 2 3 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 128 2 2 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 110 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 128 2 1 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 128 (accept_3_2 1 110 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 128))))))))))))))))))) (allB_succ' 20 109 128 (Eq.refl Bool.true) (allA_of_3_0 20
  109 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 108 128 (Eq.refl Bool.true) (allA_succ_of_gcd 20 108
  128 4 5 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  108 128 (accept_3_2 19 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 128 2 9 54 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 128
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 17 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 128 4 4 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 108 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 108 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 128 2 7 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 128 (accept_3_2 13 108 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 128 4 3 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 128 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 108
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 128 2 5 54 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 128
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 128 4 2 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 128 (accept_3_2 7 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108
  128 2 3 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  108 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 128 4 1 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 128 (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 108 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 128 2 1 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 128 (accept_3_2 1 108 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 128))))))))))))))))))))) (allB_succ' 22 107 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 107 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 128 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 107
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 128 (accept_3_2 19 107
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 128
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 107 128 (Polychromatic418967fa.accept_19_17_12_14_1_3655 17 107 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 128 (accept_3_2 16 107 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 128 (accept_3_2 13 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 128 (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 107 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 128 (accept_3_2 10 107 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 128
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 128 (accept_3_2 7 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 128 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 107 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 128 (accept_3_2 4 107 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 128
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 128 (accept_3_2 1 107 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  128)))))))))))))))))))))) (allB_succ' 23 106 128 (Eq.refl Bool.true) (allA_of_3_0 23 106 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 105 128 (Eq.refl Bool.true) (allA_succ_of_accept 23 105 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 128 (accept_3_2 22 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 105 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 105 128 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 105 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 128 (accept_3_2 19 105 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 128 (accept_3_2 16 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 105 128 (Polychromatic418967fa.accept_19_15_10_14_1_3652 15 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 105 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 128 (accept_3_2 13 105 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 128 (accept_3_2 10 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  105 128 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 128 (accept_3_2 7 105 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 105 128 (accept_3_2 4 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 105 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 128 (accept_3_2 1 105 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 128)))))))))))))))))))))))) (allB_succ' 25 104 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 104 128 8 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 128 (Polychromatic418967fa.accept_19_4_9_14_1_1345 23 104 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 128 2 11 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 21
  104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 128 4 5 26 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 128 (accept_3_2 19
  104 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 128 2 9 52 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 128 8 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 104 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 128 2 7 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 128 (accept_3_2 13 104 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 128 4 3 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 128 2 5 52 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 128
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 128 8 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 128 (accept_3_2 7 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  128 2 3 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 128 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 104 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 128 4 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 104 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 128 2 1 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 128 (accept_3_2 1 104 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 128))))))))))))))))))))))))) (allB_succ' 26 103 128 (Eq.refl Bool.true)
  (allA_of_3_0 26 103 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 102 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 102 128 2 13 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 128 (accept_3_2 25 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 128 2 12 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 128 2 11 51 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 128
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 128 2 10 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 128 (accept_3_2 19 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 128 2 9 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 128 2 8 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 128 2 7 51 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 128 (accept_3_2 13
  102 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 128 2 6 51 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 128
  (Polychromatic418967fa.accept_15_11_12_8_1_739 11 102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 128 2 5 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 128 2 4 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 128 (accept_3_2 7 102 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 128 2 3 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 128 2 2 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 128 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  102 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 128 2 1 51 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 128 (accept_3_2 1
  102 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 128))))))))))))))))))))))))))) (allB_succ' 28 101 128
  (Eq.refl Bool.true) (allA_succ_of_accept 27 101 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 128
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 128 (accept_3_2 25 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 128 (Polychromatic418967fa.accept_19_5_6_14_1_5010 24 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 128 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 128 (accept_3_2 22 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 128
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 128 (accept_3_2 19 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 128 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 128 (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 128 (accept_3_2 16 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 128
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 128 (accept_3_2 13 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 128 (Polychromatic418967fa.accept_19_11_6_14_1_6362 11 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 128 (accept_3_2 10 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 128 (accept_3_2 7 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 128 (accept_3_2 4 101 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 128
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 128 (accept_3_2 1 101 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  128)))))))))))))))))))))))))))) (allB_succ' 29 100 128 (Eq.refl Bool.true) (allA_of_3_0 29 100 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 99 128 (Eq.refl Bool.true) (allA_succ_of_accept 29 99 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 128 (accept_3_2 28 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 128 (Polychromatic418967fa.accept_19_7_4_14_1_5003 26 99 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 128 (accept_3_2 25 99 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 99 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 128 (accept_3_2 22 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 128 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 99 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 128 (accept_3_2 19 99 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 128 (accept_3_2 16 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 128 (Polychromatic418967fa.accept_19_15_4_14_1_6400 15 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 128 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 99 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 128 (accept_3_2 13 99 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 128 (Polychromatic418967fa.accept_17_12_14_9_1_5079 12 99 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 128 (accept_3_2 10 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 128 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 128 (Polychromatic418967fa.accept_14_8_1_2_1_965 8 99 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 128 (accept_3_2 7 99 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 99 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 128 (accept_3_2 4 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 99 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 128 (Polychromatic418967fa.accept_15_2_9_8_1_736 2 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 128 (accept_3_2 1 99 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 99 128)))))))))))))))))))))))))))))) (allB_succ' 31 98 128 (Eq.refl Bool.true) (allA_succ_of_gcd
  30 98 128 2 15 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 98 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 98 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 128 2 14 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 128 (Polychromatic418967fa.accept_13_1_7_11_1_702
  27 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 128 2 13 49 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 128 (accept_3_2 25
  98 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 128 2 12 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 128 2 11 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 98 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 98 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 128 2 10 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 128 (accept_3_2 19 98 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 128 2 9 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 98 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 128 2 8 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 128
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 128 2 7 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 128 (accept_3_2 13 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  128 2 6 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 128 2 5 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 128 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 98 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 128 2 4 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 128 (accept_3_2 7 98 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 128 2 3 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 128 2 2 49 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 128
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 128 2 1 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 128 (accept_3_2 1 98 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  128))))))))))))))))))))))))))))))) (allB_succ' 32 97 128 (Eq.refl Bool.true) (allA_of_3_0 32 97 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 96 128 (Eq.refl Bool.true) (allA_succ_of_gcd 32 96 128 32 1 3 4
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 128
  (accept_3_2 31 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 128 2 15 48 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 128
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 128 4 7 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 96 128 (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 96 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 128 2 13 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 128 (accept_3_2 25 96 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 128 8 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 96 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 128 2 11 48 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 128 4 5 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 128 (accept_3_2 19 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  128 2 9 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 128 16 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 128 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 96 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 128 2 7 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 128 (accept_3_2 13 96 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 128 4 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 96 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 96 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 128 2 5 48 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 128
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 128 8 1 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 128 (accept_3_2 7 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 128
  2 3 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  128 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 128 4 1 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 96 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 128 2 1 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 128 (accept_3_2 1 96 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 128))))))))))))))))))))))))))))))))) (allB_succ' 34 95 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 95 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 95 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 95 128 (accept_3_2 31 95 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 95 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 30
  95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 95 128
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 95 128 (accept_3_2 28 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  95 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 95 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 95 128 (accept_3_2 25 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 95 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 95 128
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 95 128 (accept_3_2 22 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  95 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 95 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 95 128 (accept_3_2 19 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 128 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 95 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 95 128 (accept_3_2 16 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  95 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 95 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 128 (accept_3_2 13 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 95 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 95 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 128
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 95 128 (accept_3_2 10 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  95 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 95 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 128 (accept_3_2 7 95 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 95 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 95 128
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 95 128 (accept_3_2 4 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 95 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 128 (accept_3_2 1 95 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 95 128)))))))))))))))))))))))))))))))))) (allB_succ' 35 94 128 (Eq.refl Bool.true) (allA_of_3_0
  35 94 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 93 128 (Eq.refl Bool.true) (allA_succ_of_accept 35
  93 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 93 128 (accept_3_2 34 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 93 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 93 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 128 (accept_3_2 31 93 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 128 (Polychromatic418967fa.accept_12_6_9_8_1_165
  30 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 128 (accept_3_2 28 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 128 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 128 (accept_3_2 25 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 128 (accept_3_2 22 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 128 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 128 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 128 (accept_3_2 19 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 128 (accept_3_2 16 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 128 (accept_3_2 13 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 128 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 93 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 128 (accept_3_2 10 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 128 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 128 (accept_3_2 7 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 128 (accept_3_2 4 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  128 (Polychromatic418967fa.accept_13_3_2_11_1_1999 3 93 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 93 128 (Polychromatic418967fa.accept_19_2_17_14_1_6399 2 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 128 (accept_3_2 1 93 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 93 128)))))))))))))))))))))))))))))))))))) (allB_succ' 37 92 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 92 128 4 9 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 92 128 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 92 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 128 2 17 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 128 (Polychromatic418967fa.accept_13_7_1_11_1_732
  33 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 128 4 8 23 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 128 (accept_3_2 31
  92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 128 2 15 46 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 128
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 92 128 4 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 92 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 92 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 128 2 13 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 128 (accept_3_2 25 92 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 128 4 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 92 128 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 92 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 128 2 11 46 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 128
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 128 4 5 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 128 (accept_3_2 19 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  128 2 9 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 128 4 4 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 128 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 92 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 128 2 7 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 128 (accept_3_2 13 92 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 128 4 3 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 128 (Polychromatic418967fa.accept_19_11_16_14_1_3553 11 92 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 128 2 5 46 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 128
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 128 4 2 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 128 (accept_3_2 7 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 128
  2 3 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  128 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 92 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 92 128 4 1 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 92 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 92 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 128 2 1 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 128 (accept_3_2 1 92 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 92 128))))))))))))))))))))))))))))))))))))) (allB_succ' 38 91 128 (Eq.refl Bool.true)
  (allA_of_3_0 38 91 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 90 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 90 128 2 19 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 128 (accept_3_2 37 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90
  128 2 18 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  90 128 (Polychromatic418967fa.accept_20_15_10_8_1_6398 35 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 90 128 2 17 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 90 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 128 2 16 45 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 128 (accept_3_2 31 90 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 128 2 15 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 128 2 14 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 90 128 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 128 2 13 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 128 (accept_3_2 25 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 128 2 12 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 128 (Polychromatic418967fa.accept_13_10_12_11_1_731 23 90
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 128 2 11 45 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 128
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 128 2 10 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 128 (accept_3_2 19 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90
  128 2 9 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  90 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 90 128 2 8 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 90 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 128 2 7 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 128 (accept_3_2 13 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 128 2 6 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 90 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 90 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 128 2 5 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 128
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 128 2 4 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 128 (accept_3_2 7 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 128
  2 3 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90
  128 (Polychromatic418967fa.accept_20_5_10_8_1_6397 5 90 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 128 2 2 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 128 2 1 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 128 (accept_3_2 1 90 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 90 128))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 89 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 89 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 89 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 128 (accept_3_2 37 89 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 128 (Polychromatic418967fa.accept_15_6_14_8_1_245
  36 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 128
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 128 (accept_3_2 34 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 128 (accept_3_2 31 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 128
  (Polychromatic418967fa.accept_17_12_4_9_1_3889 29 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 128 (accept_3_2 28 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 128 (accept_3_2 25 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 89 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 128 (accept_3_2 22 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 128 (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 89 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 128 (accept_3_2 19 89 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 89 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 128 (accept_3_2 16 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 128 (accept_3_2 13 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 128
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 128 (accept_3_2 10 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 128 (Polychromatic418967fa.accept_18_8_17_2_1_1557 8 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 128 (accept_3_2 7 89 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 128 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 128 (accept_3_2 4 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 128 (accept_3_2 1 89 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 128)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 88 128 (Eq.refl Bool.true)
  (allA_of_3_0 41 88 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 87 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 87 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 128 (accept_3_2 40 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 87 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 128 (Polychromatic418967fa.accept_17_4_2_9_1_3896
  38 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 128 (accept_3_2 37
  87 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 87 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 87 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 128 (accept_3_2 34 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 87 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 32
  87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 128 (accept_3_2 31 87
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 87 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 87 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 128 (accept_3_2 28 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 87 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 26
  87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 87 128 (accept_3_2 25 87
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 87 128
  (Polychromatic418967fa.accept_17_7_2_9_1_6396 24 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 87 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 128 (accept_3_2 22 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 87 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 128 (accept_3_2 19 87
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 87 128
  (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 87 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 128 (accept_3_2 16 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 87 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 14
  87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 128 (accept_3_2 13 87
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 87 128
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 87 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 128 (accept_3_2 10 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 87 128 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 87 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 87
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87 128 (accept_3_2 7 87 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 87 128 (accept_3_2 4 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87
  128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 87 128 (Polychromatic418967fa.accept_13_2_9_11_1_258 2 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 128 (accept_3_2 1 87 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 87 128)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 86 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 86 128 2 21 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 86 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 86 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 128 2 20 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 39
  86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 128 2 19 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 128 (accept_3_2 37
  86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 128 2 18 43 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 86 128 2 17 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 86 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 86 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 128 2 16 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 128 (accept_3_2 31 86 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 128 2 15 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 86 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 128 2 14 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 128
  (Polychromatic418967fa.accept_11_5_9_7_1_411 27 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 128 2 13 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 128 (accept_3_2 25 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86
  128 2 12 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  86 128 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 86 128 2 11 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 86 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 128 2 10 43 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 128 (accept_3_2 19 86 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 128 2 9 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 128 2 8 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 128
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 128 2 7 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 128 (accept_3_2 13 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  128 2 6 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 128 2 5 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 128 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 86 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 128 2 4 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 128 (accept_3_2 7 86 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 128 2 3 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 128 (Polychromatic418967fa.accept_11_5_9_7_1_411 5 86 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 128 2 2 43 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 128
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 128 2 1 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 128 (accept_3_2 1 86 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  128))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 85 128 (Eq.refl Bool.true) (allA_of_3_0 44 85 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 84 128 (Eq.refl Bool.true) (allA_succ_of_gcd 44 84 128 4 11 21
  32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 128
  (accept_3_2 43 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 128 2 21 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 84 128 4 10 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 84 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 128 2 19 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 128 (accept_3_2 37 84 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 128 4 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 84 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 128 2 17 42 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 128
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 128 4 8 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 128 (accept_3_2 31 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84
  128 2 15 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  84 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 84 128 4 7 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 128 (Polychromatic418967fa.accept_17_10_16_9_1_5127 27 84 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 128 2 13 42 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 128 (accept_3_2 25 84 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 128 4 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 23
  84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 128 2 11 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 128
  (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 128 4 5 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 128 (accept_3_2 19 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  128 2 9 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 128 4 4 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 128 2 7 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 128 (accept_3_2 13 84 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 128 4 3 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 128 (Polychromatic418967fa.accept_23_11_15_13_1_6395 11 84 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 128 2 5 42 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 128
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 128 4 2 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 128 (accept_3_2 7 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 128
  2 3 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  128 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 128 4 1 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 128 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 128 2 1 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 128 (accept_3_2 1 84 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 128))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 83 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 128 (Polychromatic418967fa.accept_19_6_7_14_1_1343 44 83
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 128 (accept_3_2 43 83 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 128 (Polychromatic418967fa.accept_13_3_5_11_1_716
  42 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 128
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 128 (accept_3_2 40 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 128 (accept_3_2 37 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 128
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 128 (accept_3_2 34 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 128 (accept_3_2 31 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 128 (Polychromatic418967fa.accept_19_11_7_14_1_6394 30 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 128 (accept_3_2 28 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 128 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 128 (accept_3_2 25 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 128
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 128 (accept_3_2 22 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 128 (Polychromatic418967fa.accept_13_7_5_11_1_1927 20 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 128 (accept_3_2 19 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 83 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 128 (accept_3_2 16 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 128 (accept_3_2 13 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 128 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 128
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 128 (accept_3_2 10 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 128 (accept_3_2 7 83 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 128 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 83 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 128
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 128 (accept_3_2 4 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 128 (accept_3_2 1 83 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 128)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 82 128 (Eq.refl Bool.true)
  (allA_of_3_0 47 82 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 81 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 128 (accept_3_2 46 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 128 (Polychromatic418967fa.accept_21_3_18_2_1_4750 45 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 128
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 44 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 128 (accept_3_2 43 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 128 (accept_3_2 40 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 128 (Polychromatic418967fa.accept_10_9_1_8_1_755 39 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 128
  (Polychromatic418967fa.accept_17_4_13_9_1_921 38 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 128 (accept_3_2 37 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 128 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 128 (accept_3_2 34 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 128
  (Polychromatic418967fa.accept_15_2_6_8_1_754 32 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 128 (accept_3_2 31 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 128 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 128 (accept_3_2 28 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 128
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 128 (accept_3_2 25 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 128 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 128 (accept_3_2 22 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 128 (Polychromatic418967fa.accept_13_8_3_11_1_3467 21 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 128
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 128 (accept_3_2 19 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 128 (accept_3_2 16 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 128 (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 128
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 128 (accept_3_2 13 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 128 (accept_3_2 10 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 128 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 81 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 128
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 128 (accept_3_2 7 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  128 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 128 (accept_3_2 4 81 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 128 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 81 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 128 (Polychromatic418967fa.accept_13_2_3_11_1_1287
  2 81 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 128 (accept_3_2 1 81
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 128))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 80 128 (Eq.refl Bool.true) (allA_succ_of_gcd 48 80 128 16 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 47
  80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 128 2 23 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 128
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 128 4 11 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 128 (accept_3_2 43 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  128 2 21 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 128 8 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 80 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 128 2 19 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 128 (accept_3_2 37 80 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 128 4 9 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 128 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 80 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 128 2 17 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 128
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 128 16 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 128 (accept_3_2 31 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  128 2 15 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 128 4 7 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 80 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 128 2 13 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 128 (accept_3_2 25 80 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 128 8 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 128 2 11 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 128
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 128 4 5 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 128 (accept_3_2 19 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  128 2 9 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 128 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 128 16 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 80 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 128 2 7 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 128 (accept_3_2 13 80 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 128 4 3 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 128 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 80 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 128 2 5 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 128
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 128 8 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 128 (accept_3_2 7 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 128
  2 3 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 80 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 128 4 1 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 128 2 1 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 128 (accept_3_2 1 80 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 128))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 79 128 (Eq.refl
  Bool.true) (allA_of_3_0 50 79 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 78 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 78 128 2 25 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 128 (accept_3_2 49 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78
  128 2 24 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  78 128 (Polychromatic418967fa.accept_17_13_10_9_1_946 47 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 78 128 2 23 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 78 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 78 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 128 2 22 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 128 (accept_3_2 43 78 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 128 2 21 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 128
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 128 2 20 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 78 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 128 2 19 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 128 (accept_3_2 37 78 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 128 2 18 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 128 2 17 39 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 128
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 128 2 16 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 128 (accept_3_2 31 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78
  128 2 15 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  78 128 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 78 128 2 14 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 78 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 78 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 128 2 13 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 128 (accept_3_2 25 78 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 128 2 12 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 128
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 128 2 11 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 78 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 128 2 10 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 128 (accept_3_2 19 78 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 128 2 9 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 78 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 78 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 128 2 8 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 128 2 7 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 128 (accept_3_2 13 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  128 2 6 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 128 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 128 2 5 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 128 2 4 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 128 (accept_3_2 7 78 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 128 2 3 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 78 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 128 2 2 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 128
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 128 2 1 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 128 (accept_3_2 1 78 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  128))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 77 128 (Eq.refl Bool.true) (allA_succ_of_accept
  51 77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 128 (accept_3_2 49 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 128
  (Polychromatic418967fa.accept_14_5_7_2_1_468 47 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 128 (accept_3_2 46 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 128 (accept_3_2 43 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 128
  (Polychromatic418967fa.accept_21_20_14_2_1_6393 41 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 128 (accept_3_2 40 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 128 (accept_3_2 37 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 128 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 128 (accept_3_2 34 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 128 (Polychromatic418967fa.accept_19_13_1_14_1_3634 32 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 128 (accept_3_2 31 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 128
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 128 (accept_3_2 28 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 128 (accept_3_2 25 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 128
  (Polychromatic418967fa.accept_13_10_12_11_1_731 23 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 128 (accept_3_2 22 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 128 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 128 (accept_3_2 19 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 128 (Polychromatic418967fa.accept_19_18_1_14_1_4978 18 77
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 128 (accept_3_2 16 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 128 (accept_3_2 13 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 128
  (Polychromatic418967fa.accept_20_11_17_8_1_4903 11 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 128 (accept_3_2 10 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 128 (accept_3_2 7 77 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 128
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 128 (accept_3_2 4 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 128 (accept_3_2 1 77 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 128)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 76 128 (Eq.refl
  Bool.true) (allA_of_3_0 53 76 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 75 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 75 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 128 (accept_3_2 52 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 50
  75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 128 (accept_3_2 49 75
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 128
  (Polychromatic418967fa.accept_18_12_3_2_1_756 48 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 128 (accept_3_2 46 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 44
  75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 128 (accept_3_2 43 75
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 128
  (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 128 (accept_3_2 40 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 38
  75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 128 (accept_3_2 37 75
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 128
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 128 (accept_3_2 34 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 128 (accept_3_2 31 75
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 128
  (Polychromatic418967fa.accept_12_6_3_8_1_512 30 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 128 (accept_3_2 28 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 128 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 26
  75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 128 (accept_3_2 25 75
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 128 (Polychromatic418967fa.accept_7_3_5_2_1_17
  24 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 75 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 128 (accept_3_2 22 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  75 128 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 75 128 (Polychromatic418967fa.accept_19_1_18_14_1_6392 20 75 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 128 (accept_3_2 19 75 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 75 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 128 (accept_3_2 16 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  75 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 75 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 128 (accept_3_2 13 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 75 128 (accept_3_2 10 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  75 128 (Polychromatic418967fa.accept_18_9_3_2_1_3814 9 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 128 (accept_3_2 7 75 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 75 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 128 (accept_3_2 4 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 75
  128 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 75 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 75 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 128 (accept_3_2 1 75 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 75 128)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 74 128 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 74 128 2 27 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 74 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 128 2 26 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 128
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 128 2 25 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 74 128 (accept_3_2 49 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74
  128 2 24 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  74 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 74 128 2 23 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 74 128 (Polychromatic418967fa.accept_20_5_14_8_1_6391 45 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 128 2 22 37 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 128 (accept_3_2 43 74 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 128 2 21 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 128
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 74 128 2 20 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 74 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 74 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 128 2 19 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 128 (accept_3_2 37 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 128 2 18 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 128 2 17 37 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 128
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 128 2 16 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 74 128 (accept_3_2 31 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74
  128 2 15 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  74 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 74 128 2 14 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 74 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 128 2 13 37 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 128 (accept_3_2 25 74 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 128 2 12 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 128
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 128 2 11 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 128 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 74 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 128 2 10 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 128 (accept_3_2 19 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 128 2 9 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 128 2 8 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 128
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 128 2 7 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 128 (accept_3_2 13 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  128 2 6 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 128 2 5 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 128 2 4 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 128 (accept_3_2 7 74 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 128 2 3 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 74 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 128 2 2 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 128
  (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 128 2 1 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 128 (accept_3_2 1 74 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  128))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 73 128 (Eq.refl Bool.true) (allA_of_3_0 56
  73 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 72 128 (Eq.refl Bool.true) (allA_succ_of_gcd 56 72 128
  8 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72
  128 (accept_3_2 55 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 128 2 27 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 128
  (Polychromatic418967fa.accept_13_1_7_11_1_702 53 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 128 4 13 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 128 (Polychromatic418967fa.accept_13_12_7_11_1_1935 51 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 128 2 25 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 128 (accept_3_2 49 72 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 128 8 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 72 128 (Polychromatic418967fa.accept_17_13_4_9_1_6390 47 72 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 128 2 23 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 128
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 128 4 11 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 128 (accept_3_2 43 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  128 2 21 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 128 (Polychromatic418967fa.accept_15_11_12_8_1_739 41 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 128 8 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 72 128 (Polychromatic418967fa.accept_19_1_15_14_1_5032 39 72 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 128 2 19 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 128 (accept_3_2 37 72 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 128 4 9 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 128 (Polychromatic418967fa.accept_10_5_2_8_1_135 35
  72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 128 2 17 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 128
  (Polychromatic418967fa.accept_15_3_12_8_1_738 33 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 128 8 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 128 (accept_3_2 31 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  128 2 15 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 128 (Polychromatic418967fa.accept_13_3_7_11_1_1904 29 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 128 4 7 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 128 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 72 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 128 2 13 36 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 128 (accept_3_2 25 72 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 128 8 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 128 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 72 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 128 2 11 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 128
  (Polychromatic418967fa.accept_27_21_18_20_1_6389 21 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 128 4 5 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 72 128 (accept_3_2 19 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 128 2 9 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 128 (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 128 8 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 128 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 72 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 128 2 7 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 128 (accept_3_2 13 72 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 128 4 3 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 128 (Polychromatic418967fa.accept_15_11_12_8_1_739
  11 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 128 2 5 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 128
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 128 8 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 128 (accept_3_2 7 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 128
  2 3 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  128 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 72 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 128 4 1 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 128 (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 128 2 1 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 128 (accept_3_2 1 72 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 128))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 71 128 (Eq.refl
  Bool.true) (allA_succ_of_accept 57 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 128 (Polychromatic418967fa.accept_13_4_6_11_1_2017
  56 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 128 (accept_3_2 55
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 128
  (Polychromatic418967fa.accept_26_2_19_24_1_6388 54 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 71 128 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 128 (accept_3_2 52 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 50
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 128 (accept_3_2 49 71
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 128
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 71 128 (Polychromatic418967fa.accept_13_8_6_11_1_1979 47 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 128 (accept_3_2 46 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 128 (Polychromatic418967fa.accept_13_5_6_11_1_1933
  44 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 128 (accept_3_2 43
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 128
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 71 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 128 (accept_3_2 40 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 128 (accept_3_2 37 71
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 128
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 71 128 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 128 (accept_3_2 34 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 128 (accept_3_2 31 71
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 128
  (Polychromatic418967fa.accept_9_3_8_2_1_162 30 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 71 128 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 128 (accept_3_2 28 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 128 (Polychromatic418967fa.accept_12_2_11_8_1_504
  26 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 128 (accept_3_2 25
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 128
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 71 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 128 (accept_3_2 22 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 128 (accept_3_2 19 71
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 128
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 71 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 128 (accept_3_2 16 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 14
  71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 128 (accept_3_2 13 71
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 128
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 71 128 (Polychromatic418967fa.accept_17_11_3_9_1_6387 11 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 128 (accept_3_2 10 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 71 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 128 (Polychromatic418967fa.accept_13_8_6_11_1_1979
  8 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 128 (accept_3_2 7 71
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 128 (Polychromatic418967fa.accept_7_6_1_2_1_230
  6 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 128 (accept_3_2 4 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 128 (accept_3_2 1 71 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 128)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 70 128 (Eq.refl
  Bool.true) (allA_of_3_0 59 70 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 69 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 69 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 128 (accept_3_2 58 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 69 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 128 (Polychromatic418967fa.accept_21_14_6_2_1_4793
  56 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 69 128 (accept_3_2 55
  69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 69 128
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 69 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 128 (accept_3_2 52 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 69 128 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 128 (accept_3_2 49 69
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 69 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 69 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 128 (accept_3_2 46 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 69 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 44
  69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 69 128 (accept_3_2 43 69
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 69 128
  (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 69 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 128 (accept_3_2 40 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 69 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 128 (accept_3_2 37 69
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 69 128 (Polychromatic418967fa.accept_7_1_6_2_1_18
  36 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 128 (accept_3_2 34 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  69 128 (Polychromatic418967fa.accept_13_7_4_11_1_1967 33 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 69 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 69 128 (accept_3_2 31 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 69 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 128 (accept_3_2 28 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  69 128 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 69 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 128 (accept_3_2 25 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 69 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 69 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 69 128 (accept_3_2 22 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  69 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 69 128 (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 69 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 69 128 (accept_3_2 19 69 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 69 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 69 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 69 128 (accept_3_2 16 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  69 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 69 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 128 (accept_3_2 13 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 69 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 128 (accept_3_2 10 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  69 128 (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 69 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 128 (accept_3_2 7 69 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 69 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 69 128 (accept_3_2 4 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69
  128 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 69 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 69 128 (Polychromatic418967fa.accept_13_2_4_11_1_2003 2 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 128 (accept_3_2 1 69 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 69 128)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 68 128
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 68 128 4 15 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 68 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 128 2 29 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 128
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 128 4 14 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 128 (accept_3_2 55 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  128 2 27 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 128 4 13 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 128 2 25 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 128 (accept_3_2 49 68 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 128 4 12 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 128
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 128 2 23 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 68 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 128 4 11 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 128 (accept_3_2 43 68 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 128 2 21 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 128 (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 68 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 128 4 10 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 128
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 128 2 19 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 128 (accept_3_2 37 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  128 4 9 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 128 2 17 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 128 4 8 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 128 (accept_3_2 31 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 128 2 15 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 128 (Polychromatic418967fa.accept_18_11_14_2_1_5058
  29 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 128 4 7 17 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 128
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 128 2 13 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 128 (accept_3_2 25 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  128 4 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 128 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 128 2 11 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 128 4 5 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 128 (accept_3_2 19 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 128 2 9 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 68 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 128 4 4 17 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 128
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 128 2 7 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 128 (accept_3_2 13 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  128 4 3 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 128 2 5 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 128 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 68 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 128 4 2 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 128 (accept_3_2 7 68 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 128 2 3 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 128 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 68 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 128 4 1 17 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 128 2 1 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 128 (accept_3_2 1 68 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 67 128 (Eq.refl Bool.true)
  (allA_of_3_0 62 67 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 66 128 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 66 128 2 31 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 128 (accept_3_2 61 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66
  128 2 30 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  66 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 66 128 2 29 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 66 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 66 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 128 2 28 33 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 128 (accept_3_2 55 66 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 128 2 27 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 66 128 2 26 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 66 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 66 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 128 2 25 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 128 (accept_3_2 49 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 128 2 24 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 66 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 128 2 23 33 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 128
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 128 2 22 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 128 (accept_3_2 43 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66
  128 2 21 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  66 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 66 128 2 20 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 66 128 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 128 2 19 33 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 128 (accept_3_2 37 66 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 128 2 18 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 66 128 2 17 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 66 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 66 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 128 2 16 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 128 (accept_3_2 31 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 128 2 15 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 66 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 128 2 14 33 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 128
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 128 2 13 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 128 (accept_3_2 25 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66
  128 2 12 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  66 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 66 128 2 11 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 66 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 128 2 10 33 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 128 (accept_3_2 19 66 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 128 2 9 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 128 2 8 33 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 128 2 7 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 128 (accept_3_2 13 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66
  128 2 6 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  66 128 (Polychromatic418967fa.accept_19_11_9_14_1_6386 11 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 66 128 2 5 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 66 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 128 2 4 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 128 (accept_3_2 7 66 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 128 2 3 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 66 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 66 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 128 2 2 33 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 128
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 128 2 1 33 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 128 (accept_3_2 1 66 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 65 128 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 65 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 128 (accept_3_2 61 65 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 128 (Polychromatic418967fa.accept_14_4_9_2_1_95 60
  65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 128
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 59 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 128 (accept_3_2 58 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 128 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 128 (accept_3_2 55 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 128 (Polychromatic418967fa.accept_20_14_5_8_1_4870 54 65
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 128
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 128 (accept_3_2 52 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 128 (accept_3_2 49 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 128 (Polychromatic418967fa.accept_15_3_5_8_1_1387 48 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 128
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 128 (accept_3_2 46 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 128 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 128 (accept_3_2 43 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 65 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 128
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 128 (accept_3_2 40 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 128 (accept_3_2 37 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 128 (Polychromatic418967fa.accept_11_3_10_7_1_129 36 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 128
  (Polychromatic418967fa.accept_14_7_9_2_1_2489 35 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 128 (accept_3_2 34 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 128 (accept_3_2 31 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 128 (Polychromatic418967fa.accept_20_10_5_8_1_6385 30 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 128
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 128 (accept_3_2 28 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 128 (accept_3_2 25 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 128 (Polychromatic418967fa.accept_19_5_8_14_1_6384 24 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 128
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 128 (accept_3_2 22 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 128 (Polychromatic418967fa.accept_25_20_15_3_1_6383 20 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 128 (accept_3_2 19 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 128 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 65 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 128
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 128 (accept_3_2 16 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 128 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 128 (accept_3_2 13 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 128
  (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 128 (accept_3_2 10 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 128 (Polychromatic418967fa.accept_26_8_13_24_1_6381 8 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 128 (accept_3_2 7 65 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 128 (Polychromatic418967fa.accept_19_6_8_14_1_2351 6 65 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 128
  (Polychromatic418967fa.accept_17_5_14_9_1_5104 5 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 128 (accept_3_2 4 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 128 (accept_3_2 1 65 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 128)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 128
  (allA_of_3_0 64 64 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 128 (allA_succ_of_accept 62 63 128
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 62 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 128 (accept_3_2 61 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 128 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 128 (accept_3_2 58 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 128 (Polychromatic418967fa.accept_15_12_3_8_1_5245 57 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 128
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 128 (accept_3_2 55 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 128 (accept_3_2 52 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 128 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 128
  (Polychromatic418967fa.accept_15_5_3_8_1_748 50 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 128 (accept_3_2 49 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 128 (Polychromatic418967fa.accept_11_4_8_7_1_819 48 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 128 (accept_3_2 46 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 128 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 128
  (Polychromatic418967fa.accept_24_20_15_8_1_6380 44 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 128 (accept_3_2 43 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 128 (accept_3_2 40 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 128 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 128
  (Polychromatic418967fa.accept_17_4_12_9_1_6379 38 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 128 (accept_3_2 37 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 128 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 128 (accept_3_2 34 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 128 (Polychromatic418967fa.accept_14_5_7_2_1_468 33 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 128
  (Polychromatic418967fa.accept_26_6_11_24_1_6378 32 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 128 (accept_3_2 31 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 128 (accept_3_2 28 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 128 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 128
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 128 (accept_3_2 25 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 128 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 128 (accept_3_2 22 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 128 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 128
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 128 (accept_3_2 19 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 128 (accept_3_2 16 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 128 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 128
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 128 (accept_3_2 13 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 128 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 128 (accept_3_2 10 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 128 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 128
  (Polychromatic418967fa.accept_19_8_6_14_1_5009 8 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 128 (accept_3_2 7 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  128 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 128 (accept_3_2 4 63 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 128 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 63 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 128
  (Polychromatic418967fa.accept_24_2_15_8_1_6377 2 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 128 (accept_3_2 1 63 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 128 (allA_succ_of_accept 61 62 128
  (accept_3_2 61 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 128 2 30 31 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 128 2 29 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 128 2 28 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 128 (accept_3_2 55 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 128 2 27 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 62 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 128 2 26 31 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 128
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 128 2 25 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 128 (accept_3_2 49 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  128 2 24 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 128 2 23 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 128 2 22 31 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 128 (accept_3_2 43 62 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 128 2 21 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 128 2 20 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 128 2 19 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 128 (accept_3_2 37 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 128 2 18 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 128 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 62 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 128 2 17 31 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 128
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 128 2 16 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 128 (accept_3_2 31 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  128 2 15 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 128 2 14 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 128 (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 128 2 13 31 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 128 (accept_3_2 25 62 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 128 2 12 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 128 2 11 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 128 2 10 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 128 (accept_3_2 19 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 128 2 9 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 128 2 8 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 128 2 7 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 128 (accept_3_2 13 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  128 2 6 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 128 2 5 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 128 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 128 2 4 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 128 (accept_3_2 7 62 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 128 2 3 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 128 2 2 31 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 128 2 1 31 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 128 (accept_3_2 1 62 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  128)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 128 (allA_of_3_0 61 61 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 128 (allA_succ_of_accept 59 60 128
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 128 2 29 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 128 4 14 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 128 (accept_3_2 55 60 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 128 2 27 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 128 4 13 15 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 128
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 128 2 25 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 128 (accept_3_2 49 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  128 4 12 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 128 2 23 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 128 (Polychromatic418967fa.accept_13_6_8_11_1_5398 45 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 128 4 11 15 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 128 (accept_3_2 43 60 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 128 2 21 30 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 128
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 128 4 10 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 128 2 19 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 128 (accept_3_2 37 60 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 128 4 9 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 128 2 17 30 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 128
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 128 4 8 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 128 (accept_3_2 31 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  128 2 15 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 128 (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 128 4 7 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 60 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 128 2 13 30 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 128 (accept_3_2 25 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 128 4 6 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 128 2 11 30 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 128 4 5 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 128 (accept_3_2 19 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  128 2 9 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 128 4 4 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 128 (Polychromatic418967fa.accept_21_15_18_2_1_6376 15 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 128 2 7 30 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 128 (accept_3_2 13 60 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 128 4 3 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 128 (Polychromatic418967fa.accept_19_11_3_14_1_6375 11 60
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 128 2 5 30 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 128
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 128 4 2 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 128 (accept_3_2 7 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 128
  2 3 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 60 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 128 4 1 15 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 128 2 1 30 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 128 (accept_3_2 1 60 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 128)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 128
  (allA_succ_of_accept 58 59 128 (accept_3_2 58 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 128 (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 128 (accept_3_2 55 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 59 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 128 (accept_3_2 52 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 128 (accept_3_2 49 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 128
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 128 (accept_3_2 46 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 128 (accept_3_2 43 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 128
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 128 (accept_3_2 40 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 128 (accept_3_2 37 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 128 (accept_3_2 34 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 128 (Polychromatic418967fa.accept_21_11_17_2_1_4749 32 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 128 (accept_3_2 31 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 128 (accept_3_2 28 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 128 (accept_3_2 25 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 128
  (Polychromatic418967fa.accept_17_6_8_9_1_1771 23 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 128 (accept_3_2 22 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 128 (accept_3_2 19 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 128 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 128 (accept_3_2 16 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 128 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 128 (accept_3_2 13 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 128
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 128 (accept_3_2 10 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 128 (accept_3_2 7 59 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 59 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 128
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 128 (accept_3_2 4 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 128 (accept_3_2 1 59 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 128 (allA_of_3_0
  58 58 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 128 (allA_succ_of_accept 56 57 128
  (Polychromatic418967fa.accept_15_11_12_8_1_739 56 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 128 (accept_3_2 55 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 128 (accept_3_2 52 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 128 (accept_3_2 49 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 128 (accept_3_2 46 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 128 (accept_3_2 43 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 128 (accept_3_2 40 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 128 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 128
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 128 (accept_3_2 37 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 128 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 128 (accept_3_2 34 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 128 (accept_3_2 31 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 128 (accept_3_2 28 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 128 (accept_3_2 25 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 128 (accept_3_2 22 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 128 (Polychromatic418967fa.accept_23_21_11_13_1_6374 21 57 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 128
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 128 (accept_3_2 19 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 128 (accept_3_2 16 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 128 (accept_3_2 13 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 128 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 128 (accept_3_2 10 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 128 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 57 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 128 (accept_3_2 7 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  128 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 128 (accept_3_2 4 57 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 57 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 128 (Polychromatic418967fa.accept_22_2_13_18_1_6373
  2 57 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 128 (accept_3_2 1 57
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 128)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 128 (allA_succ_of_accept 55 56 128 (accept_3_2 55 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 128 2 27 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 128 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 56 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 128 4 13 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 128 (Polychromatic418967fa.accept_13_12_4_11_1_1925
  51 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 128 2 25 28 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 128 (accept_3_2 49
  56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 128 8 6 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 128
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 47 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 128 2 23 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 128 (Polychromatic418967fa.accept_13_6_4_11_1_282 45 56 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 128 4 11 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 128 (accept_3_2 43 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 128 2 21 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 128 (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 56 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 128 8 5 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 128
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 128 2 19 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 128 (accept_3_2 37 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  128 4 9 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 128 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 128 2 17 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 128 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 128 8 4 7 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 128 (accept_3_2 31 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 128 2 15 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 128 (Polychromatic418967fa.accept_17_12_5_9_1_6372
  29 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 128 4 7 14 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 128
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 56 128 2 13 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 56 128 (accept_3_2 25 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56
  128 8 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  56 128 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 56 128 2 11 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 56 128 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 128 4 5 14 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 128 (accept_3_2 19 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 128 2 9 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 128 (Polychromatic418967fa.accept_11_6_1_7_1_1315 17 56 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 128 8 2 7 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 128
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 56 128 2 7 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 56 128 (accept_3_2 13 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56
  128 4 3 14 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  56 128 (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 128 2 5 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 128 (Polychromatic418967fa.accept_21_9_14_2_1_6370 9 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 128 8 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 128 (accept_3_2 7 56 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 128 2 3 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 128 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 56 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 128 4 1 14 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 128
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 128 2 1 28 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 128 (accept_3_2 1 56 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  128)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 128 (allA_of_3_0 55 55 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 54 128 (allA_succ_of_accept 53 54 128
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 128 2 26 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 128 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 54 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 128 2 25 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 128 (accept_3_2 49 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 128 2 24 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 128 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 54 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 128 2 23 27 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 128 2 22 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 128 (accept_3_2 43 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  128 2 21 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 128 (Polychromatic418967fa.accept_19_3_16_14_1_6369 41 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 128 2 20 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 54 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 128 2 19 27 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 128 (accept_3_2 37 54 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 128 2 18 27 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 128
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 128 2 17 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 128 2 16 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 128 (accept_3_2 31 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 128 2 15 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 54 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 128 2 14 27 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 128 2 13 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 128 (accept_3_2 25 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  128 2 12 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 128 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 128 2 11 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 128 2 10 27 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 128 (accept_3_2 19 54 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 128 2 9 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 128 2 8 27 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 128 2 7 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 128 (accept_3_2 13 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  128 2 6 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 128 2 5 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 128 2 4 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 128 (accept_3_2 7 54 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 128 2 3 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 128 (Polychromatic418967fa.accept_19_5_16_14_1_2374 5 54 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 128 2 2 27 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 128 2 1 27 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 128 (accept_3_2 1 54 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  128)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 128 (allA_succ_of_accept 52 53 128 (accept_3_2
  52 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 128
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 128 (accept_3_2 49 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 128 (accept_3_2 46 53
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 128
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 44 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 128 (accept_3_2 43 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 128 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 128 (accept_3_2 40 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 128
  (Polychromatic418967fa.accept_11_5_9_7_1_411 38 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 128 (accept_3_2 37 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 128 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 128 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 128 (accept_3_2 34 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 128 (accept_3_2 31 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 128 (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 128 (accept_3_2 28 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 128
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 128 (accept_3_2 25 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 128 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 128 (accept_3_2 22 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 128
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 128 (accept_3_2 19 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 128 (Polychromatic418967fa.accept_19_18_15_14_1_5017 18 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 128 (Polychromatic418967fa.accept_19_17_15_14_1_3623 17 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 128 (accept_3_2 16 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 128 (accept_3_2 13 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 128 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 128 (accept_3_2 10 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 128
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 128 (accept_3_2 7 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  128 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 128 (accept_3_2 4 53 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 128 (Polychromatic418967fa.accept_11_2_9_7_1_124 2
  53 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 128 (accept_3_2 1 53 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 128)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 128 (allA_of_3_0 52 52 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 128
  (allA_succ_of_accept 50 51 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 128 (accept_3_2 49 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 128 (accept_3_2 46 51
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 128
  (Polychromatic418967fa.accept_21_3_9_2_1_6368 45 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 128 (accept_3_2 43 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41
  51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 128 (accept_3_2 40 51
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 128 (Polychromatic418967fa.accept_20_18_11_8_1_6367 38 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 128 (accept_3_2 37 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 128 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 51 128 (accept_3_2 34 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  51 128 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 51 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 128 (accept_3_2 31 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 51 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 51 128 (accept_3_2 28 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  51 128 (Polychromatic418967fa.accept_13_1_12_11_1_728 27 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 51 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 128 (accept_3_2 25 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 51 128 (Polychromatic418967fa.accept_19_5_13_14_1_6366 24 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 128 (accept_3_2 22 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 128 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 128 (accept_3_2 19 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 128 (accept_3_2 16 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 128 (Polychromatic418967fa.accept_19_15_13_14_1_5015 15 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 128 (accept_3_2 13 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 128 (accept_3_2 10 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 128 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 128 (accept_3_2 7 51 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 51 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 128
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 128 (accept_3_2 4 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 128 (Polychromatic418967fa.accept_15_2_6_8_1_754 2 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 128 (accept_3_2 1 51 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 128))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 128 (allA_succ_of_accept
  49 50 128 (accept_3_2 49 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 128 2 24 25 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 128
  (Polychromatic418967fa.accept_12_11_2_8_1_511 47 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 128 2 23 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 128 2 22 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 128 (accept_3_2 43 50 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 128 2 21 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 50 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 128 2 20 25 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 128
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 128 2 19 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 128 (accept_3_2 37 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  128 2 18 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 128 2 17 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 50 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 128 2 16 25 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 128 (accept_3_2 31 50 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 128 2 15 25 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 128
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 128 2 14 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 128 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 128 2 13 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 128 (accept_3_2 25 50 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 128 2 12 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 128 (Polychromatic418967fa.accept_11_1_6_7_1_116 23 50 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 128 2 11 25 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 128
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 128 2 10 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 128 (accept_3_2 19 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  128 2 9 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 128 2 8 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 50 128 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 50 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 128 2 7 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 128 (accept_3_2 13 50 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 128 2 6 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 50 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 128 2 5 25 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 128
  (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 128 2 4 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 128 (accept_3_2 7 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 128
  2 3 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50
  128 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 50 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 128 2 2 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 128 2 1 25 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 128 (accept_3_2 1 50 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 128)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 128 (allA_of_3_0 49 49
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 128 (allA_succ_of_accept 47 48 128
  (Polychromatic418967fa.accept_11_3_4_7_1_114 47 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 128 2 23 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 48 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 128 4 11 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 128 (accept_3_2 43 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 128 2 21 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 128 8 5 6 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 128
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 128 2 19 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 128 (accept_3_2 37 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48
  128 4 9 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  48 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 48 128 2 17 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 48 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 128 16 2 3 8 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 128 (accept_3_2 31 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 128 2 15 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 128 4 7 12 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 128
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 128 2 13 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 128 (accept_3_2 25 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  128 8 3 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 128 2 11 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 128 (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 128 4 5 12 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 128 (accept_3_2 19 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 128 2 9 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 48 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 128 16 1 3 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 128 2 7 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 128 (accept_3_2 13 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  128 4 3 12 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 128 2 5 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 128 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 128 8 1 6 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 128 (accept_3_2 7 48 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 128 2 3 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 128 4 1 12 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 128 2 1 24 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 128 (accept_3_2 1 48 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  128)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 128 (allA_succ_of_accept 46 47 128 (accept_3_2 46 47
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 128
  (Polychromatic418967fa.accept_17_10_13_9_1_3913 44 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 128 (accept_3_2 43 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 128 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 128 (Polychromatic418967fa.accept_19_3_9_14_1_3595 41 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 128 (accept_3_2 40 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 128 (accept_3_2 37 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 128 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 128 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 128 (accept_3_2 34 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 128
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 128 (accept_3_2 31 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 128 (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 128 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 128 (accept_3_2 28 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 128
  (Polychromatic418967fa.accept_11_4_3_7_1_828 26 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 128 (accept_3_2 25 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 128 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 128 (accept_3_2 22 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 128
  (Polychromatic418967fa.accept_19_1_9_14_1_526 20 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 128 (accept_3_2 19 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 128 (accept_3_2 16 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 128
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 128 (accept_3_2 13 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 128 (Polychromatic418967fa.accept_19_12_9_14_1_6365 12 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 128 (accept_3_2 10 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 128
  (Polychromatic418967fa.accept_19_8_9_14_1_6364 8 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 128 (accept_3_2 7 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  128 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 128 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 128 (accept_3_2 4 47 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 128
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 128 (accept_3_2 1 47 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  128))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 128 (allA_of_3_0 46 46 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 128 (allA_succ_of_accept 44 45 128 (Polychromatic418967fa.accept_13_5_6_11_1_1933
  44 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 128 (accept_3_2 43
  45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 128
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 128 (accept_3_2 40 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 128 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 128 (Polychromatic418967fa.accept_21_17_3_2_1_2111
  38 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 128 (accept_3_2 37
  45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 128 (accept_3_2 34 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 128 (Polychromatic418967fa.accept_10_2_5_8_1_139
  32 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 128 (accept_3_2 31
  45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 128
  (Polychromatic418967fa.accept_12_6_9_8_1_165 30 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 128 (accept_3_2 28 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 26
  45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 128 (accept_3_2 25 45
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 128
  (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 128 (accept_3_2 22 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 45 128 (Polychromatic418967fa.accept_13_8_6_11_1_1979 21 45 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 128
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 128 (accept_3_2 19 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 128 (accept_3_2 16 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 45 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 128
  (Polychromatic418967fa.accept_20_14_5_8_1_4870 14 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 128 (accept_3_2 13 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 128 (accept_3_2 10 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 128 (Polychromatic418967fa.accept_21_9_3_2_1_6363 9 45 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 128 (accept_3_2 7 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  128 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 128 (accept_3_2 4 45 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 128 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 45 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  45 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 128 (accept_3_2 1 45 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 128))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  128 (allA_succ_of_accept 43 44 128 (accept_3_2 43 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 128 2 21 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 128 4 10 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 128 2 19 22 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 128 (accept_3_2 37 44 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 128 4 9 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 128 (Polychromatic418967fa.accept_15_5_14_8_1_1376
  35 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 128 2 17 22 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 128
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 128 4 8 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 128 (accept_3_2 31 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  128 2 15 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 128 4 7 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 128 (Polychromatic418967fa.accept_19_8_6_14_1_5009 27 44 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 128 2 13 22 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 128 (accept_3_2 25 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 128 4 6 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 128 2 11 22 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 128
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 128 4 5 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 128 (accept_3_2 19 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  128 2 9 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 128 (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 128 4 4 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 128 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 44 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 128 2 7 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 128 (accept_3_2 13 44 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 128 4 3 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 128 (Polychromatic418967fa.accept_19_11_6_14_1_6362 11 44 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 128 2 5 22 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 128
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 128 4 2 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 128 (accept_3_2 7 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 128
  2 3 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 128 4 1 11 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 44 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 128 2 1 22 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 128 (accept_3_2 1 44 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 128)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 128 (allA_of_3_0 43 43 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 128 (allA_succ_of_accept 41 42 128
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 128 2 20 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 128 2 19 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 128 (accept_3_2 37 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 128 2 18 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 128 2 17 21 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 128
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 128 2 16 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 128 (accept_3_2 31 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42
  128 2 15 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  42 128 (Polychromatic418967fa.accept_19_10_4_14_1_4981 29 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 42 128 2 14 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 128 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 42 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 128 2 13 21 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 128 (accept_3_2 25 42 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 128 2 12 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 128
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 128 2 11 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 42 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 128 2 10 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 128 (accept_3_2 19 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 128 2 9 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 42 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 128 2 8 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 128
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 128 2 7 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 128 (accept_3_2 13 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42
  128 2 6 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  42 128 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 128 2 5 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 42 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 128 2 4 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 128 (accept_3_2 7 42 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 128 2 3 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 42 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 128 2 2 21 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 128 2 1 21 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 128 (accept_3_2 1 42 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  128)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 128 (allA_succ_of_accept 40 41 128 (accept_3_2 40 41 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 128 (accept_3_2 37 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 128 (accept_3_2 34 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 128
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 128 (accept_3_2 31 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 128 (accept_3_2 28 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 128 (accept_3_2 25 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 128 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 128 (accept_3_2 22 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 128
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 128 (accept_3_2 19 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 128 (accept_3_2 16 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 128
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 128 (accept_3_2 13 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 128 (accept_3_2 10 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 128 (accept_3_2 7 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  128 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 128 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 128 (accept_3_2 4 41 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  41 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 128 (accept_3_2 1 41 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 128))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 128
  (allA_of_3_0 40 40 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 128 (allA_succ_of_accept 38 39 128
  (Polychromatic418967fa.accept_22_16_17_18_1_6361 38 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 39 128 (accept_3_2 37 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 128 (Polychromatic418967fa.accept_19_17_1_14_1_6360 36 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 128 (accept_3_2 34 39 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 33
  39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 128 (accept_3_2 31 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 128 (accept_3_2 28 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 39 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 128
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 128 (accept_3_2 25 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 128 (accept_3_2 22 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 128 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 39 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 128
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 128 (accept_3_2 19 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 128 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 128 (accept_3_2 16 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 128 (accept_3_2 13 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 128 (accept_3_2 10 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 128 (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 39 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 128 (accept_3_2 7 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  128 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 128 (accept_3_2 4 39 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 128 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 39 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 128 (Polychromatic418967fa.accept_15_2_9_8_1_736 2
  39 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 128 (accept_3_2 1 39 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 128))))))))))))))))))))))))))))))))))))))) (allB_succ 38 128
  (allA_succ_of_accept 37 38 128 (accept_3_2 37 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  128 2 18 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 128 2 17 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 38 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 128 2 16 19 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 128 (accept_3_2 31 38 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 128 2 15 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 128 2 14 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 128 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 38 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 128 2 13 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 128 (accept_3_2 25 38 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 128 2 12 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 38 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 128 2 11 19 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 128
  (Polychromatic418967fa.accept_20_1_18_8_1_6359 21 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 128 2 10 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 128 (accept_3_2 19 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  128 2 9 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 128 2 8 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 38 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 128 2 7 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 128 (accept_3_2 13 38 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 128 2 6 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 128 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 128 2 5 19 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 128
  (Polychromatic418967fa.accept_11_9_5_7_1_815 9 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 128 2 4 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 128 (accept_3_2 7 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 128
  2 3 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 38 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 128 2 2 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 128 (Polychromatic418967fa.accept_20_3_18_8_1_4859 3 38 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 128 2 1 19 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 128 (accept_3_2 1 38 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 128)))))))))))))))))))))))))))))))))))))) (allB_succ 37 128 (allA_of_3_0 37 37 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 128 (allA_succ_of_accept 35 36 128
  (Polychromatic418967fa.accept_19_16_17_14_1_4969 35 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 36 128 2 17 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 36 128 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 128 4 8 9 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 128 (accept_3_2 31 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 128 2 15 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 128 (Polychromatic418967fa.accept_13_3_10_11_1_1293
  29 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 128 4 7 9 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 128
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 128 2 13 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 128 (accept_3_2 25 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  128 4 6 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 128 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 128 2 11 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 128 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 128 4 5 9 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 128 (accept_3_2 19 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 128 2 9 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 36 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 128 4 4 9 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 128
  (Polychromatic418967fa.accept_11_4_3_7_1_828 15 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 128 2 7 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 128 (accept_3_2 13 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  128 4 3 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 128 (Polychromatic418967fa.accept_17_11_2_9_1_6358 11 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 128 2 5 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 128 (Polychromatic418967fa.accept_19_9_17_14_1_6357 9 36 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 128 4 2 9 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 128 (accept_3_2 7 36 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 128 2 3 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 128 (Polychromatic418967fa.accept_19_5_17_14_1_3627 5 36 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 128 4 1 9 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 128
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 128 2 1 18 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 128 (accept_3_2 1 36 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  128)))))))))))))))))))))))))))))))))))) (allB_succ 35 128 (allA_succ_of_accept 34 35 128 (accept_3_2 34 35 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 128 (accept_3_2 31 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 128 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 35 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 128 (accept_3_2 28 35 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 128
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 128 (accept_3_2 25 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 128 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 128 (accept_3_2 22 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 128
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 20 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 128 (accept_3_2 19 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 128 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 128 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 128 (accept_3_2 16 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 128 (accept_3_2 13 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 128 (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 35 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 128 (accept_3_2 10 35 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 128
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 128 (accept_3_2 7 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  128 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 128 (accept_3_2 4 35 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  35 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 128 (accept_3_2 1 35 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 128))))))))))))))))))))))))))))))))))) (allB_succ 34 128
  (allA_of_3_0 34 34 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 128 (allA_succ_of_accept 32 33 128
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 128 (accept_3_2 31 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 128 (accept_3_2 28 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 128 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 128
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 128 (accept_3_2 25 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 128 (accept_3_2 22 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 128
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 128 (accept_3_2 19 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 128 (accept_3_2 16 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 128 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 128
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 128 (accept_3_2 13 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 128 (accept_3_2 10 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 128 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 128
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 128 (accept_3_2 7 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  128 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 33 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 128 (accept_3_2 4 33 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 33 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 128
  (Polychromatic418967fa.accept_25_2_8_3_1_6356 2 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 33 128 (accept_3_2 1 33 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  128))))))))))))))))))))))))))))))))) (allB_succ 32 128 (allA_succ_of_accept 31 32 128 (accept_3_2 31 32 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 128 2 15 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 128 (Polychromatic418967fa.accept_18_11_14_2_1_5058
  29 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 32 128 4 7 8 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 32 128
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 32 128 2 13 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 32 128 (accept_3_2 25 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32
  128 8 3 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  32 128 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 32 128 2 11 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 32 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 128 4 5 8 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 128 (accept_3_2 19 32 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 128 2 9 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 32 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 128 16 1 2 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 128
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 128 2 7 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 128 (accept_3_2 13 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  128 4 3 8 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 128 (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 128 2 5 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 128 (Polychromatic418967fa.accept_14_9_4_2_1_983 9 32 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 128 8 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 128 (accept_3_2 7 32 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 128 2 3 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 32 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 128 4 1 8 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 128
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 128 2 1 16 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 128 (accept_3_2 1 32 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  128)))))))))))))))))))))))))))))))) (allB_succ 31 128 (allA_of_3_0 31 31 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 128 (allA_succ_of_accept 29 30 128 (Polychromatic418967fa.accept_22_7_8_18_1_6355 29 30 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 128 2 14 15 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 128 2 13 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 128 (accept_3_2 25 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30
  128 2 12 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  30 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 128 2 11 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 128 2 10 15 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 128 (accept_3_2 19 30 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 128 2 9 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 128 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 128 2 8 15 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 128
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 128 2 7 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 128 (accept_3_2 13 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30
  128 2 6 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  30 128 (Polychromatic418967fa.accept_21_11_9_2_1_6354 11 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 128 2 5 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 128 2 4 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 128 (accept_3_2 7 30 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 128 2 3 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 30 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 128 2 2 15 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 128 2 1 15 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 128 (accept_3_2 1 30 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  128)))))))))))))))))))))))))))))) (allB_succ 29 128 (allA_succ_of_accept 28 29 128 (accept_3_2 28 29 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 128
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 128 (accept_3_2 25 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 128 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 29 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 128 (accept_3_2 22 29 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 128
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 128 (accept_3_2 19 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 128 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 128 (accept_3_2 16 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 128
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 128 (accept_3_2 13 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 128 (Polychromatic418967fa.accept_19_12_10_14_1_6353 12 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 128 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 128 (accept_3_2 10 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 128
  (Polychromatic418967fa.accept_13_8_3_11_1_3467 8 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 128 (accept_3_2 7 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  128 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 29 128 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 128 (accept_3_2 4 29 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 29 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  29 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 128 (accept_3_2 1 29 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29 128))))))))))))))))))))))))))))) (allB_succ 28 128 (allA_of_3_0
  28 28 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 27 128 (allA_succ_of_accept 26 27 128
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 128 (accept_3_2 25 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  27 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 27 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 128 (accept_3_2 22 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 128 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 27 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 128
  (Polychromatic418967fa.accept_11_9_5_7_1_815 20 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 128 (accept_3_2 19 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 128 (accept_3_2 16 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 27 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 128
  (Polychromatic418967fa.accept_21_14_6_2_1_4793 14 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 128 (accept_3_2 13 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 128 (Polychromatic418967fa.accept_13_12_1_11_1_1917 12 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 128 (accept_3_2 10 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 128 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 27 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 128
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 128 (accept_3_2 7 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  128 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 128 (accept_3_2 4 27 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 27 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 128 (Polychromatic418967fa.accept_19_2_8_14_1_3648
  2 27 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 128 (accept_3_2 1 27
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 128))))))))))))))))))))))))))) (allB_succ 26 128
  (allA_succ_of_accept 25 26 128 (accept_3_2 25 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  128 2 12 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 128 2 11 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 128 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 128 2 10 13 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 128 (accept_3_2 19 26 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 128 2 9 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 128 2 8 13 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 128
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 128 2 7 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 128 (accept_3_2 13 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  128 2 6 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 128 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 128 2 5 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 128 (Polychromatic418967fa.accept_23_9_3_13_1_6352 9 26 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 128 2 4 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 128 (accept_3_2 7 26 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 128 2 3 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 128 2 2 13 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 128
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 128 2 1 13 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 128 (accept_3_2 1 26 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  128)))))))))))))))))))))))))) (allB_succ 25 128 (allA_of_3_0 25 25 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 128 (allA_succ_of_accept 23 24 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 24 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 128 2 11 12 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 128
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 128 4 5 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 128 (accept_3_2 19 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  128 2 9 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 128 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 128 8 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 128 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 24 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 128 2 7 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 128 (accept_3_2 13 24 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 128 4 3 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 128 (Polychromatic418967fa.accept_19_11_5_14_1_6351 11 24 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 128 2 5 12 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 128
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 128 8 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 128 (accept_3_2 7 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 128
  2 3 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 24 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 128 4 1 6 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 128 2 1 12 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 128 (accept_3_2 1 24 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 128)))))))))))))))))))))))) (allB_succ 23 128 (allA_succ_of_accept 22 23 128 (accept_3_2 22
  23 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 128
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 128 (Polychromatic418967fa.accept_17_3_6_9_1_2761 20 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 128 (accept_3_2 19 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 128 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 23 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 128 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 128 (accept_3_2 16 23
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 128 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 128
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 128 (accept_3_2 13 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 128 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 23 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 128 (accept_3_2 10 23 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 128
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 128 (accept_3_2 7 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  128 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 128 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 128 (accept_3_2 4 23 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 128 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  23 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 128 (accept_3_2 1 23 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 128))))))))))))))))))))))) (allB_succ 22 128 (allA_of_3_0 22 22
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 128 (allA_succ_of_accept 20 21 128
  (Polychromatic418967fa.accept_19_1_2_14_1_3666 20 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 128 (accept_3_2 19 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 128 (accept_3_2 16 21 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 128 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 128
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 128 (accept_3_2 13 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 128 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 128 (accept_3_2 10 21 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 128 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 128
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 128 (accept_3_2 7 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  128 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 128 (accept_3_2 4 21 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 128 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 21 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 128 (Polychromatic418967fa.accept_15_2_6_8_1_754 2
  21 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 128 (accept_3_2 1 21 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 128))))))))))))))))))))) (allB_succ 20 128 (allA_succ_of_accept
  19 20 128 (accept_3_2 19 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 128 2 9 10 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 128 4 4 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 128 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 20 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 128 2 7 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 128 (accept_3_2 13 20 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 128 4 3 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 128 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 20 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 128 2 5 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 128 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9
  20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 128 4 2 5 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 128 (accept_3_2 7 20
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 128 2 3 10 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 128
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 20 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 128 4 1 5 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 128 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 20 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 128 2 1 10 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 128 (accept_3_2 1 20 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 128)))))))))))))))))))) (allB_succ 19 128 (allA_of_3_0 19 19 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 128 (allA_succ_of_accept 17 18 128 (Polychromatic418967fa.accept_27_17_18_20_1_6350 17 18
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 128 2 8 9 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 128 2 7 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 128 (accept_3_2 13 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  128 2 6 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 128 (Polychromatic418967fa.accept_15_11_3_8_1_750 11 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 128 2 5 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 128 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 128 2 4 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 128 (accept_3_2 7 18 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 128 2 3 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 18 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 128 2 2 9 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 128
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 128 2 1 9 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 128 (accept_3_2 1 18 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  128)))))))))))))))))) (allB_succ 17 128 (allA_succ_of_accept 16 17 128 (accept_3_2 16 17 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 128
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 128 (accept_3_2 13 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 128 (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 17 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 128 (accept_3_2 10 17 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 128
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 128 (accept_3_2 7 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  128 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 128 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 17 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 128 (accept_3_2 4 17 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 128 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  17 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 128 (accept_3_2 1 17 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 128))))))))))))))))) (allB_succ 16 128 (allA_of_3_0 16 16 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 128 (allA_succ_of_accept 14 15 128
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 128 (accept_3_2 13 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 128 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 128 (accept_3_2 10 15 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 128 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 15 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 128
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 128 (accept_3_2 7 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  128 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 128 (accept_3_2 4 15 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 15 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  15 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 128 (accept_3_2 1 15 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 128))))))))))))))) (allB_succ 14 128 (allA_succ_of_accept 13 14
  128 (accept_3_2 13 14 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 128 2 6 7 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 128
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 128 2 5 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 128 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 14 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 128 2 4 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 128 (accept_3_2 7 14 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 128 2 3 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 128 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 128 2 2 7 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 128 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 128 2 1 7 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 128 (accept_3_2 1 14
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 128)))))))))))))) (allB_succ 13 128 (allA_of_3_0 13 13 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 128 (allA_succ_of_accept 11 12 128
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 12 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 128 2 5 6 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 128 (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 12 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 128 4 2 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 128 (accept_3_2 7 12 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 128 2 3 6 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 128 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 128 4 1 3 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 128 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 12
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 128 2 1 6 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 128 (accept_3_2 1 12
  128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 128)))))))))))) (allB_succ 11 128 (allA_succ_of_accept 10 11
  128 (accept_3_2 10 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 128
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 128 (Polychromatic418967fa.accept_17_8_11_9_1_5099 8 11 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 128 (accept_3_2 7 11 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 128 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 11 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 128 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 128 (accept_3_2 4 11 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 128
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 128 (accept_3_2 1 11 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  128))))))))))) (allB_succ 10 128 (allA_of_3_0 10 10 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 128
  (allA_succ_of_accept 8 9 128 (Polychromatic418967fa.accept_13_8_9_11_1_1265 8 9 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 128 (accept_3_2 7 9 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 128 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 128 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 128 (accept_3_2 4 9 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 128 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3
  9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 128
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 128 (accept_3_2 1 9 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 128)))))))))
  (allB_succ 8 128 (allA_succ_of_accept 7 8 128 (accept_3_2 7 8 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 128 2 3 4 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 128 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 8 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 128 4 1 2 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 128 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 8 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 128 2 1 4 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 128 (accept_3_2 1 8 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 128)))))))) (allB_succ 7 128 (allA_of_3_0 7 7 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 128 (allA_succ_of_accept 5 6 128 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 128 2 2 3 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 128
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 6 128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 128 2 1 3 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 128 (accept_3_2 1 6 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 128))))))
  (allB_succ 5 128 (allA_succ_of_accept 4 5 128 (accept_3_2 4 5 128 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 128 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 128 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 128 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 5 128
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 128 (accept_3_2 1 5 128 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 128))))) (allB_succ 4 128 (allA_of_3_0 4 4 128 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 128 (allA_succ_of_accept 2 3 128 (Polychromatic418967fa.accept_13_2_3_11_1_1287 2 3
  128 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 128 (accept_3_2 1 3 128
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 128))) (allB_succ 2 128 (allA_succ_of_accept 1 2 128 (accept_3_2
  1 2 128 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 128)) (allB_two
  128))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


