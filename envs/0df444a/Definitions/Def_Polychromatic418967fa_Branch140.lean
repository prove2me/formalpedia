-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch140
-- name    : Polychromatic418967fa_Branch140
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:03.71517+00:00
-- url     : https://prove2.me/theorems/09b02c82-710e-4c2a-adfe-0d09dc520c4d
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

def Polychromatic418967fa.branch_140 : allB 140 140 :=
  allB_succ' 2 139 140 (Eq.refl Bool.true) (allA_of_3_0 2 139 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  138 140 (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 140 2 1 69 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 140 (accept_3_2 1 138 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138 140))) (allB_succ' 4 137 140 (Eq.refl Bool.true) (allA_succ_of_accept 3 137 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 137 140 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 137 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 140 (accept_3_2 1 137 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 137 140)))) (allB_succ' 5 136 140 (Eq.refl Bool.true) (allA_of_3_0 5 136 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 135 140 (Eq.refl Bool.true) (allA_succ_of_gcd 5 135 140 5 1 27 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 140 (accept_3_2 4
  135 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 140
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 140 (Polychromatic418967fa.accept_13_2_5_10_1_250 2 135 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 140 (accept_3_2 1 135 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 140)))))) (allB_succ' 7 134 140 (Eq.refl Bool.true) (allA_succ_of_gcd 6 134 140 2 3 67 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 140
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 134 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 134 140 2 2 67 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 134 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 134 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 140 2 1 67 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 140 (accept_3_2 1 134 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 134 140))))))) (allB_succ' 8 133 140 (Eq.refl Bool.true) (allA_of_3_0 8 133 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 132 140 (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 140 4 2 33 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 140
  (accept_3_2 7 132 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 140 2 3 66 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 140
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 132 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 140 4 1 33 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 132 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 132 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 140 2 1 66 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 140 (accept_3_2 1 132 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132 140))))))))) (allB_succ' 10 131 140 (Eq.refl Bool.true) (allA_succ_of_accept 9 131 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 131 140 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 131 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 140 (accept_3_2 7 131 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 131 140 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 131 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 140 (Polychromatic418967fa.accept_19_5_17_7_1_7252
  5 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 140 (accept_3_2 4
  131 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 131 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 131 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 140 (accept_3_2 1 131 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 131 140)))))))))) (allB_succ' 11 130 140 (Eq.refl Bool.true) (allA_of_3_0 11 130 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 129 140 (Eq.refl Bool.true) (allA_succ_of_accept 11 129 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 140 (accept_3_2 10 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 140 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 129 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 140 (accept_3_2 7 129 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 129 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 140 (accept_3_2 4 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 140 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 129 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 140 (accept_3_2 1 129 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 140)))))))))))) (allB_succ' 13 128 140 (Eq.refl Bool.true) (allA_succ_of_gcd 12 128
  140 4 3 32 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  128 140 (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 128 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 140 2 5 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 140 (Polychromatic418967fa.accept_21_9_2_14_1_7251 9 128 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 140 4 2 32 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 140 (accept_3_2 7 128 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 140 2 3 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 140 (Polychromatic418967fa.accept_26_5_24_10_1_7250 5 128
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 140 4 1 32 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 128 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 140 2 1 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 140 (accept_3_2 1 128 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  140))))))))))))) (allB_succ' 14 127 140 (Eq.refl Bool.true) (allA_of_3_0 14 127 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 126 140 (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 140 14 1 9 10 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 140 (accept_3_2 13 126 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 140 2 6 63 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 140
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 126 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 140 2 5 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 126 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 140 2 4 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 140 7 1 18 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 140 2 3 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 140 (Polychromatic418967fa.accept_19_5_12_7_1_4416 5 126 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 140 2 2 63 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 140
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 126 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 140 2 1 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 140 (accept_3_2 1 126 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  140))))))))))))))) (allB_succ' 16 125 140 (Eq.refl Bool.true) (allA_succ_of_gcd 15 125 140 5 3 25 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 125 140
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 140 (accept_3_2 13 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 125 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 140 5 2 25 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 140 (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 125 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 140 (accept_3_2 7 125 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 140 5 1 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 140 (accept_3_2 4 125 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 140 (accept_3_2 1 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  140)))))))))))))))) (allB_succ' 17 124 140 (Eq.refl Bool.true) (allA_of_3_0 17 124 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 123 140 (Eq.refl Bool.true) (allA_succ_of_accept 17 123 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 140 (accept_3_2 16 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 140 (Polychromatic418967fa.accept_25_14_23_15_1_7249 14 123 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 140 (accept_3_2 13 123 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 123 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 140 (accept_3_2 10 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 140 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 123 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 140 (accept_3_2 7 123 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 123 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 140 (accept_3_2 4 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 123 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 140 (accept_3_2 1 123 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 140)))))))))))))))))) (allB_succ' 19 122 140 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 122 140 2 9 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 122 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 140 2 8 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 140 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  15 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 140 2 7 61 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 140
  (accept_3_2 13 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 140 2 6 61 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 140 2 5 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 140 (Polychromatic418967fa.accept_19_9_8_7_1_2061 9 122 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 140 2 4 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 140 (accept_3_2 7 122 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 140 2 3 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 140 2 2 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 140 (Polychromatic418967fa.accept_15_3_2_5_1_2980 3
  122 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 140 2 1 61 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 140 (accept_3_2 1
  122 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 140))))))))))))))))))) (allB_succ' 20 121 140 (Eq.refl
  Bool.true) (allA_of_3_0 20 121 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 120 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 120 140 20 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 140 (accept_3_2 19 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 140 2 9 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 120 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 120 140 4 4 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 140 5 3 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 140 2 7 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 120 140 (accept_3_2 13 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 120 140 4 3 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 120 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 120 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 140 10 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 140 (Polychromatic418967fa.accept_11_9_10_8_1_444 9
  120 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 140 4 2 30 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 140 (accept_3_2 7
  120 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 140 2 3 60 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 140 5 1 24 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 120 140 4 1 30 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 140
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 120 140 2 1 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 140 (accept_3_2 1 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  140))))))))))))))))))))) (allB_succ' 22 119 140 (Eq.refl Bool.true) (allA_succ_of_gcd 21 119 140 7 3 17 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 119 140
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 140 (accept_3_2 19 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 140 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 140 (accept_3_2 16 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 119 140 7 2 17 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 119 140 (accept_3_2 13 119 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 140 (Polychromatic418967fa.accept_9_3_2_5_1_234
  12 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 140
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 140 (accept_3_2 10 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 119 140 7 1 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 119 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 140
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 140 (accept_3_2 4 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 140 (accept_3_2 1 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 119 140)))))))))))))))))))))) (allB_succ' 23 118 140 (Eq.refl Bool.true) (allA_of_3_0
  23 118 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 117 140 (Eq.refl Bool.true) (allA_succ_of_accept 23
  117 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 140 (accept_3_2 22 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 117 140 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 140 (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 117
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 140 (accept_3_2 19 117
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 140
  (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 140 (accept_3_2 16 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 140 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 117 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 140
  (Polychromatic418967fa.accept_19_14_3_7_1_7248 14 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 140 (accept_3_2 13 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 117 140 (Polychromatic418967fa.accept_19_12_3_7_1_5832 12 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 140 (accept_3_2 10 117 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 140
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 140 (accept_3_2 7 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  117 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 117 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 140 (accept_3_2 4 117 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 140 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 117 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 140
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 140 (accept_3_2 1 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  140)))))))))))))))))))))))) (allB_succ' 25 116 140 (Eq.refl Bool.true) (allA_succ_of_gcd 24 116 140 4 6 29 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 140
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 116 140 2 11 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 116 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 116 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 140 4 5 29 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 140 (accept_3_2 19 116 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 140 2 9 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 140 (Polychromatic418967fa.accept_15_2_11_5_1_1266
  17 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 140 4 4 29 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 140 2 7 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 116 140 (accept_3_2 13 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  116 140 4 3 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 116 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 140 2 5 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 140 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 116 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 140 4 2 29 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 140 (accept_3_2 7 116 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 140 2 3 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 140 (Polychromatic418967fa.accept_16_5_4_12_1_3800 5 116 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 140 4 1 29 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 140 2 1 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 140 (accept_3_2 1 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  140))))))))))))))))))))))))) (allB_succ' 26 115 140 (Eq.refl Bool.true) (allA_of_3_0 26 115 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 114 140 (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 140 2 13 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 140 (accept_3_2 25
  114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 140 2 12 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 140
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 140 2 11 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 114 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 140 2 10 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 140 (accept_3_2 19 114 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 140 2 9 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 140 2 8 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 140
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 114 140 2 7 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 114 140 (accept_3_2 13 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  114 140 2 6 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 114 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 114 140 2 5 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 114 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 140 2 4 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 140 (accept_3_2 7 114 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 140 2 3 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 140 (Polychromatic418967fa.accept_21_5_9_14_1_7247 5 114 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 140 2 2 57 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 114 140 2 1 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 140 (accept_3_2 1 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  140))))))))))))))))))))))))))) (allB_succ' 28 113 140 (Eq.refl Bool.true) (allA_succ_of_accept 27 113 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 113 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 140 (accept_3_2 25 113 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 140 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 113 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 140
  (Polychromatic418967fa.accept_17_6_11_4_1_1525 23 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 140 (accept_3_2 22 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 140 (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 113 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 140 (accept_3_2 19 113 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 140 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 113
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 140
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 140 (accept_3_2 16 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 113 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 140 (accept_3_2 13 113 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 140 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 113
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 140
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 140 (accept_3_2 10 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 140 (Polychromatic418967fa.accept_16_8_1_12_1_984 8 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 140 (accept_3_2 7 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 140 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 113 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 140
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 140 (accept_3_2 4 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 140 (accept_3_2 1 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 140)))))))))))))))))))))))))))) (allB_succ' 29 112 140 (Eq.refl Bool.true)
  (allA_of_3_0 29 112 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 111 140 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 111 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 140 (accept_3_2 28 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 140 (Polychromatic418967fa.accept_9_8_3_5_1_241
  26 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 140 (accept_3_2 25
  111 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 140
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 140 (accept_3_2 22 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 140 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 111 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 140 (accept_3_2 19 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 111 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 111 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 140 (accept_3_2 16 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 111 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 140
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 111 140 (accept_3_2 13 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 111 140 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 111 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 140 (accept_3_2 10 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 140 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 111 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 140 (accept_3_2 7 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  111 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 111 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 140 (accept_3_2 4 111 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 140 (accept_3_2 1 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  140)))))))))))))))))))))))))))))) (allB_succ' 31 110 140 (Eq.refl Bool.true) (allA_succ_of_gcd 30 110 140 10 3 11 14
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 110 140
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 110 140 2 14 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 110 140 (Polychromatic418967fa.accept_19_8_15_7_1_323 27 110 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 110 140 2 13 55 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 110 140 5 5 22 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 110 140 2 12 55 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 110 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 110 140 2 11 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 110 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 110 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 140 10 2 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 140 (accept_3_2 19 110 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 110 140 2 9 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 110 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 140 2 8 55 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 110 140 5 3 22 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 110 140 2 7 55 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 140 (accept_3_2 13
  110 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 140 2 6 55 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 140 10 1 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 110 140 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 110 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 140 2 4 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 140 (accept_3_2 7 110 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 140 2 3 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 110 140 5 1 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 110 140 2 2 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 110 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 110 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 140 2 1 55 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 140 (accept_3_2 1 110 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 110 140))))))))))))))))))))))))))))))) (allB_succ' 32 109 140 (Eq.refl
  Bool.true) (allA_of_3_0 32 109 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 108 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 108 140 4 8 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 108 140 (accept_3_2 31 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  108 140 2 15 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 140 (Polychromatic418967fa.accept_21_8_3_14_1_4165 29 108 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 140 4 7 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 140 (Polychromatic418967fa.accept_13_1_4_10_1_622
  27 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 140 2 13 54 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 140
  (accept_3_2 25 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 140 4 6 27 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 140
  (Polychromatic418967fa.accept_15_8_3_5_1_608 23 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 140 2 11 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 140 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 108 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 140 4 5 27 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 140 (accept_3_2 19 108 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 140 2 9 54 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 140
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 17 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 140 4 4 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 108 140 (Polychromatic418967fa.accept_19_15_13_7_1_7246 15 108 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 140 2 7 54 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 140 (accept_3_2 13 108 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 140 4 3 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 140
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 140 2 5 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 108 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 108 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 140 4 2 27 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 140 (accept_3_2 7 108 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 140 2 3 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 140 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 108 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 140 4 1 27 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 108 140
  (Polychromatic418967fa.accept_19_3_13_7_1_7245 3 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 108 140 2 1 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 140 (accept_3_2 1 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  140))))))))))))))))))))))))))))))))) (allB_succ' 34 107 140 (Eq.refl Bool.true) (allA_succ_of_accept 33 107 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 107 140 (Polychromatic418967fa.accept_13_6_3_10_1_698 32 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 140 (accept_3_2 31 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 107 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 107 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 140 (Polychromatic418967fa.accept_9_2_8_5_1_228
  29 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 140 (accept_3_2 28
  107 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 107 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 140 (accept_3_2 25 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 107 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 107 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 140 (Polychromatic418967fa.accept_8_7_3_4_1_404
  23 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 140 (accept_3_2 22
  107 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 107 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 140 (accept_3_2 19 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 107 140 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 107 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 140
  (Polychromatic418967fa.accept_16_1_11_12_1_1774 17 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 107 140 (accept_3_2 16 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 107 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 107
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 140 (accept_3_2 13 107
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 107 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 140 (accept_3_2 10 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 107 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 140 (Polychromatic418967fa.accept_16_8_11_12_1_962
  8 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 140 (accept_3_2 7
  107 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 107 140 (Polychromatic418967fa.accept_19_5_12_7_1_4416 5 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 140 (accept_3_2 4 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 107 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 140 (accept_3_2 1 107
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107 140)))))))))))))))))))))))))))))))))) (allB_succ' 35 106
  140 (Eq.refl Bool.true) (allA_of_3_0 35 106 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 105 140
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 105 140 35 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 105 140 (accept_3_2 34 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 105 140 (Polychromatic418967fa.accept_17_16_3_4_1_6010 33 105 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 140 (Polychromatic418967fa.accept_24_8_9_20_1_7244 32 105
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 140 (accept_3_2 31 105
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 140 5 6 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 105 140 7 4 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 105 140 (Polychromatic418967fa.accept_22_5_17_8_1_7243 27 105 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 105 140 5 5 21 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 105 140
  (Polychromatic418967fa.accept_13_11_1_10_1_648 24 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 140 (accept_3_2 22 105 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 105 140 7 3 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 140 5 4 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 105 140 (accept_3_2 19 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 140 (accept_3_2 16 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 140 5 3 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 140 7 2 15 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 140 (accept_3_2 13 105 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 105 140 5 2 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 105 140 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 105 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 105 140 7 1 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 105 140
  (Polychromatic418967fa.accept_12_6_9_8_1_165 6 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 105 140 5 1 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 105 140 (accept_3_2 4 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  105 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 105 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 105 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 140 (accept_3_2 1 105 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 105 140)))))))))))))))))))))))))))))))))))) (allB_succ' 37 104 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 104 140 4 9 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 140 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 104 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 140 2 17 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 140 (Polychromatic418967fa.accept_16_1_8_12_1_405
  33 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 140 4 8 26 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 140
  (accept_3_2 31 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 140 2 15 52 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 140
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 104 140 4 7 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 104 140 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 104 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 140 2 13 52 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 140 (accept_3_2 25
  104 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 140 4 6 26 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 140
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 104 140 2 11 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 104 140 (Polychromatic418967fa.accept_15_6_14_5_1_2976 21 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 140 4 5 26 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 140 (accept_3_2 19 104 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 140 2 9 52 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 140
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 140 4 4 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 140 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 104 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 140 2 7 52 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 140 (accept_3_2 13 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 140 4 3 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 140
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 104 140 2 5 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 104 140 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 140 4 2 26 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 140 (accept_3_2 7 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104 140 2 3 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 104 140 (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 104 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 140 4 1 26 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 140
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 140 2 1 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 140 (accept_3_2 1 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  140))))))))))))))))))))))))))))))))))))) (allB_succ' 38 103 140 (Eq.refl Bool.true) (allA_of_3_0 38 103 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 102 140 (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 140 2 19 51 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 140
  (accept_3_2 37 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 102 140 2 18 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 102 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 140 2 17 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 102 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 140 2 16 51 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 140 (accept_3_2 31 102 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 140 2 15 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 140 2 14 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 140
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 140 2 13 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 140 (accept_3_2 25 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 140 2 12 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 140 (Polychromatic418967fa.accept_15_8_12_5_1_2987 23 102 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 140 2 11 51 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 140 2 10 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 140 (accept_3_2 19 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 140 2 9 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 102 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 140 2 8 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 140 2 7 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 140 (accept_3_2 13
  102 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 140 2 6 51 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 140 2 5 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 140 2 4 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 140 (accept_3_2 7 102 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 140 2 3 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 140 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 102 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 140 2 2 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 140 2 1 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 140 (accept_3_2 1
  102 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 140))))))))))))))))))))))))))))))))))))))) (allB_succ'
  40 101 140 (Eq.refl Bool.true) (allA_succ_of_accept 39 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 140
  (Polychromatic418967fa.accept_11_5_2_8_1_866 38 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 140 (accept_3_2 37 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 140 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 140 (accept_3_2 34 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 140
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 140 (accept_3_2 31 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 140 (Polychromatic418967fa.accept_21_8_17_14_1_4156 29 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 140 (accept_3_2 28 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 140 (accept_3_2 25 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 140 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 140 (accept_3_2 22 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 140
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 140 (accept_3_2 19 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 140 (Polychromatic418967fa.accept_19_18_6_7_1_5882 18 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 140 (accept_3_2 16 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 140
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 140 (accept_3_2 13 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 140 (Polychromatic418967fa.accept_22_11_13_8_1_7242 11 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 140 (accept_3_2 10 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 140 (accept_3_2 7 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 140 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 140 (accept_3_2 4 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 140
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 140 (accept_3_2 1 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  140)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 100 140 (Eq.refl Bool.true) (allA_of_3_0 41 100 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 99 140 (Eq.refl Bool.true) (allA_succ_of_accept 41 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 140 (accept_3_2 40 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 140 (Polychromatic418967fa.accept_13_12_8_10_1_1879 38 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 140 (accept_3_2 37 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 140 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 99
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 140 (accept_3_2 34 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 140 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 140 (Polychromatic418967fa.accept_19_13_4_7_1_5878 32 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 140 (accept_3_2 31 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 99 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 140 (accept_3_2 28 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 140 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 140 (Polychromatic418967fa.accept_15_11_9_5_1_2974 26 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 140 (accept_3_2 25 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 140 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 99
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 140 (accept_3_2 22 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 140 (Polychromatic418967fa.accept_18_3_9_14_1_2219 21 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 140 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 140 (accept_3_2 19 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 99 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 140 (accept_3_2 16 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 140 (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 140 (accept_3_2 13 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 140 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 99
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 140 (accept_3_2 10 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 140 (Polychromatic418967fa.accept_16_9_3_12_1_1802 9 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 99 140 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 140 (accept_3_2 7 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 99 140 (accept_3_2 4 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99
  140 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 99 140 (Polychromatic418967fa.accept_13_2_8_10_1_1902 2 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 140 (accept_3_2 1 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 99 140)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 98 140 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 98 140 14 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 98 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 98 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 98 140 2 20 49 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 98 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 98 140 2 19 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 98 140 (accept_3_2 37 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98
  140 2 18 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 98
  140 7 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 98
  140 2 17 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  98 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 98 140 2 16 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 98 140 (accept_3_2 31 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 98 140 2 15 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 98 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 98 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 140 14 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 140 (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 98 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 140 2 13 49 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 140 (accept_3_2 25
  98 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 140 2 12 49 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 140 2 11 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 98 140 7 3 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 98 140 2 10 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 98 140 (accept_3_2 19 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98
  140 2 9 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  98 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 98 140 2 8 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 98 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 98 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 98 140 14 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 98 140 (accept_3_2 13 98 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98 140 2 6 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 98 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 98 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 98 140 2 5 49 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 98 140
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 98 140 2 4 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 98 140 7 1 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 98 140 2 3 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 98 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 98 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 140 2 2 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 98 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 98 140 2 1 49 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 98 140 (accept_3_2 1 98 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98 140))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 97
  140 (Eq.refl Bool.true) (allA_of_3_0 44 97 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 96 140 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 96 140 4 11 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 96 140 (accept_3_2 43 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 140 2 21 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 140 (Polychromatic418967fa.accept_13_2_5_10_1_250 41 96 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 140 4 10 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 39
  96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 140 2 19 48 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 140 (accept_3_2 37
  96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 140 4 9 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 140 2 17 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 96 140 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 96 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 140 4 8 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 140 (accept_3_2 31 96 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 96 140 2 15 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 96 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 140 4 7 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 140
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 96 140 2 13 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 96 140 (accept_3_2 25 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96
  140 4 6 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  96 140 (Polychromatic418967fa.accept_17_6_11_4_1_1525 23 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 96 140 2 11 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 96 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 96 140 4 5 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 140 (accept_3_2 19 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 140 2 9 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 96 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 140 4 4 24 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 140
  (Polychromatic418967fa.accept_13_2_5_10_1_250 15 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 96 140 2 7 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 140 (accept_3_2 13 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96
  140 4 3 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  96 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 96 140 2 5 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 96 140 (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 96 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 96 140 4 2 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 140 (accept_3_2 7 96 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 140 2 3 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 96 140 (Polychromatic418967fa.accept_21_5_12_14_1_7241 5 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 140 4 1 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 96 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 96 140 2 1 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 96 140 (accept_3_2 1 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  140))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 95 140 (Eq.refl Bool.true) (allA_succ_of_gcd 45 95 140
  5 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 95
  140 (Polychromatic418967fa.accept_13_5_4_10_1_1244 44 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 95 140 (accept_3_2 43 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 95 140 (Polychromatic418967fa.accept_25_17_20_15_1_7240 42 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 95 140 (Polychromatic418967fa.accept_21_20_11_14_1_5718 41 95
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 95 140 5 8 19 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 95 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 95 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 95 140 (accept_3_2 37 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 95 140 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 95 140 5 7 19 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 95 140 (accept_3_2 34 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 140
  (Polychromatic418967fa.accept_13_6_4_10_1_660 32 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 140 (accept_3_2 31 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 95
  140 5 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  95 140 (Polychromatic418967fa.accept_16_13_15_12_1_1748 29 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 95 140 (accept_3_2 28 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 95 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 140 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 95 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 95 140 5 5 19 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 95 140
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 95 140 (Polychromatic418967fa.accept_17_6_10_4_1_6007 23 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 140 (accept_3_2 22 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 95 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 95 140 5 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 95 140 (accept_3_2 19 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 95 140 (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 140
  (Polychromatic418967fa.accept_25_17_20_15_1_7240 17 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 95 140 (accept_3_2 16 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 95 140 5 3 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 95 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 95 140 (accept_3_2 13 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 95 140 (Polychromatic418967fa.accept_21_12_11_14_1_7239 12 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 95 140
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 95 140 5 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 95 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 140 (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 95 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 95 140 (accept_3_2 7 95 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95 140 (Polychromatic418967fa.accept_13_6_4_10_1_660 6
  95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 95 140 5 1 19 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 95 140 (accept_3_2 4 95
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 95 140 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 140
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 95 140 (accept_3_2 1 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  140)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 94 140 (Eq.refl Bool.true) (allA_of_3_0 47 94 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 93 140 (Eq.refl Bool.true) (allA_succ_of_accept 47 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 140 (accept_3_2 46 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  93 140 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 93 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 140 (accept_3_2 43 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 93 140 (accept_3_2 40 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  93 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 93 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 140 (accept_3_2 37 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 140 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 93 140 (accept_3_2 34 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  93 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 93 140 (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 140 (accept_3_2 31 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 140 (accept_3_2 28 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  93 140 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 93 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 140 (accept_3_2 25 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 93 140 (accept_3_2 22 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  93 140 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 93 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 140 (accept_3_2 19 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 93 140 (accept_3_2 16 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  93 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 93 140 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 140 (accept_3_2 13 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 140 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 140 (accept_3_2 10 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  93 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 93 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 140 (accept_3_2 7 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 93 140 (accept_3_2 4 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93
  140 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 93 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 140 (accept_3_2 1 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 93 140)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 92 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 92 140 4 12 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 92 140 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 92 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 140 2 23 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  45 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 140 4 11 23 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 140 (accept_3_2 43
  92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 140 2 21 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 140
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 92 140 4 10 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 92 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 92 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 140 2 19 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 140 (accept_3_2 37 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 140 4 9 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 92 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 92 140 2 17 46 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 92 140
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 92 140 4 8 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 92 140 (accept_3_2 31 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92
  140 2 15 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  92 140 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 92 140 4 7 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 92 140 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 92 140 2 13 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 92 140 (accept_3_2 25 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92 140 4 6 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 92 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 92 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 92 140 2 11 46 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 92 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 92 140 4 5 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 92 140 (accept_3_2 19 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92
  140 2 9 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  92 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 92 140 4 4 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 92 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 92 140 2 7 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 92 140 (accept_3_2 13 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92 140 4 3 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 92 140 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 92 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 140 2 5 46 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 140
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 92 140 4 2 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 92 140 (accept_3_2 7 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 140
  2 3 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92
  140 (Polychromatic418967fa.accept_21_5_8_14_1_5696 5 92 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 92 140 4 1 23 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 92 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 92 140 2 1 46 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 92 140 (accept_3_2 1 92 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 92 140))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 91 140 (Eq.refl
  Bool.true) (allA_of_3_0 50 91 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 90 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 90 140 10 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 140 (accept_3_2 49 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90
  140 2 24 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  90 140 (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 90 140 2 23 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 90 140 5 9 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 90 140 2 22 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 90 140 (accept_3_2 43 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 90 140 2 21 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 90 140 (Polychromatic418967fa.accept_13_2_12_10_1_2649 41 90 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 140 10 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 90 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 140 2 19 45 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 140 (accept_3_2 37
  90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 140 2 18 45 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 90 140 5 7 18 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 90 140 2 17 45 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 90 140 2 16 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 90 140 (accept_3_2 31 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90
  140 10 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  90 140 (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 90 140 2 14 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 90 140 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 90 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 140 2 13 45 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 90 140 5 5 18 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 90 140 2 12 45 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 140
  (Polychromatic418967fa.accept_17_6_5_4_1_7238 23 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 140 2 11 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 140 10 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 140 (accept_3_2 19 90 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 90 140 2 9 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 90 140 (Polychromatic418967fa.accept_27_17_9_5_1_7237 17 90 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 140 2 8 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 140 5 3 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 140 2 7 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 140 (accept_3_2 13 90 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 140 2 6 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 90 140 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 90 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 140 10 1 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 140 2 4 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 140 (accept_3_2 7 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 140
  2 3 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 90 140 5
  1 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 90 140 2 2
  45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 140
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 140 2 1 45 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 140 (accept_3_2 1 90 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  140))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 89 140 (Eq.refl Bool.true) (allA_succ_of_accept
  51 89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 89 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 140 (accept_3_2 49 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 89 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 89 140 (accept_3_2 46 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 89 140 (Polychromatic418967fa.accept_19_6_13_7_1_4464 44 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 140 (accept_3_2 43 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 89 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 89 140
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 41 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 89 140 (accept_3_2 40 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 89 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 140 (accept_3_2 37 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 140 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 89 140
  (Polychromatic418967fa.accept_16_3_9_12_1_4831 35 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 89 140 (accept_3_2 34 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 89 140 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 140 (accept_3_2 31 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 89 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 140
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 140 (accept_3_2 28 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 140 (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 140 (accept_3_2 25 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 140
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 140 (accept_3_2 22 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 140 (accept_3_2 19 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 140 (Polychromatic418967fa.accept_16_2_9_12_1_46 18 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 140
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 140 (accept_3_2 16 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 140 (accept_3_2 13 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 140 (accept_3_2 10 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 140 (Polychromatic418967fa.accept_13_8_11_10_1_636 8 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 140 (accept_3_2 7 89 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 89 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 140
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 140 (accept_3_2 4 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 140 (accept_3_2 1 89 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 140)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 88 140 (Eq.refl
  Bool.true) (allA_of_3_0 53 88 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 87 140 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 140 (accept_3_2 52 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 87 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 140 (Polychromatic418967fa.accept_16_2_7_12_1_3793
  50 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 140 (accept_3_2 49
  87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 87 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 48 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 140 (accept_3_2 46 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 87 140 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 140 (accept_3_2 43 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 140 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 140 (accept_3_2 40 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 140 (accept_3_2 37 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 140 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 140 (accept_3_2 34 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 140 (Polychromatic418967fa.accept_19_14_11_7_1_7236 33 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 140
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 140 (accept_3_2 31 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 140 (accept_3_2 28 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 140 (accept_3_2 25 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 140 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 140 (accept_3_2 22 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 140 (accept_3_2 19 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 140 (accept_3_2 16 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 140 (Polychromatic418967fa.accept_17_15_2_4_1_2423 15 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 140
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 140 (accept_3_2 13 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 140 (accept_3_2 10 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 140 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 87 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 140 (accept_3_2 7 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 140 (accept_3_2 4 87 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  87 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 140 (accept_3_2 1 87 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 140))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 86 140 (Eq.refl Bool.true) (allA_succ_of_gcd 54 86 140 2 27 43 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 140
  (Polychromatic418967fa.accept_12_5_2_8_1_172 53 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 86 140 2 26 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 86 140 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 86 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 86 140 2 25 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 86 140 (accept_3_2 49 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86 140 2 24 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 86 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 86 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 86 140 2 23 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 86 140
  (Polychromatic418967fa.accept_21_3_2_14_1_7235 45 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 86 140 2 22 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 86 140 (accept_3_2 43 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86
  140 2 21 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  86 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 86 140 2 20 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 86 140 (Polychromatic418967fa.accept_15_9_11_5_1_1283 39 86 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 140 2 19 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 140 (accept_3_2 37 86 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 140 2 18 43 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 86 140 2 17 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 86 140 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 86 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 140 2 16 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 140 (accept_3_2 31 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 140 2 15 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 86 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 86 140 2 14 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 86 140
  (Polychromatic418967fa.accept_21_6_2_14_1_5688 27 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 86 140 2 13 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 86 140 (accept_3_2 25 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86
  140 2 12 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  86 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 86 140 2 11 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 86 140 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 86 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 140 2 10 43 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 140 (accept_3_2 19 86 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 140 2 9 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 86 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 140 2 8 43 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 140
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 140 2 7 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 140 (accept_3_2 13 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  140 2 6 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 140 2 5 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 140 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 140 2 4 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 140 (accept_3_2 7 86 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 140 2 3 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 86 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 140 2 2 43 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 140
  (Polychromatic418967fa.accept_19_3_10_7_1_5884 3 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 140 2 1 43 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 140 (accept_3_2 1 86 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 85 140 (Eq.refl Bool.true) (allA_of_3_0 56
  85 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 84 140 (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 140
  28 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84
  140 (accept_3_2 55 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 140 2 27 42 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 140 4 13 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 84 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 140 2 25 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 84 140 7 7 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 84 140 4 12 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 47
  84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 140 2 23 42 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 140
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 140 4 11 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 140 (accept_3_2 43 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84
  140 14 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  84 140 (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 84 140 4 10 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 84 140 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 84 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 140 2 19 42 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 140 (accept_3_2 37 84 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 140 4 9 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 84 140 7 5 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 84 140 2 17 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 140 4 8 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 140 (accept_3_2 31
  84 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 140 2 15 42 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 84 140 28 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 84 140 (Polychromatic418967fa.accept_15_12_9_5_1_2973 27 84 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 140 2 13 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 140 (accept_3_2 25 84 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 140 4 6 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 84 140 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 84 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 140 2 11 42 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 140 7 3 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 140 4 5 21 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 140 (accept_3_2 19 84 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 140 2 9 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 17
  84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 140 4 4 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 140
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 84 140 14 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 140 (accept_3_2 13 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84
  140 4 3 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  84 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 84 140 2 5 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 84 140 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 84 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 140 4 2 21 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 84 140 7 1 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 84 140 2 3 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 140 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5
  84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 140 4 1 21 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 140
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 140 2 1 42 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 140 (accept_3_2 1 84 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 83 140 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 140 (Polychromatic418967fa.accept_13_4_5_10_1_1247 56 83
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 140 (accept_3_2 55 83 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 140 (Polychromatic418967fa.accept_13_2_5_10_1_250
  54 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 140 (accept_3_2 52 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 140 (accept_3_2 49 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 140
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 140 (accept_3_2 46 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 140 (accept_3_2 43 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 140
  (Polychromatic418967fa.accept_13_2_5_10_1_250 41 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 140 (accept_3_2 40 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 140 (accept_3_2 37 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 140 (accept_3_2 34 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 140 (Polychromatic418967fa.accept_13_6_5_10_1_1213 32 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 140 (accept_3_2 31 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 83 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 140
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 29 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 140 (accept_3_2 28 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 140 (accept_3_2 25 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 140
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 140 (accept_3_2 22 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 140 (Polychromatic418967fa.accept_16_4_3_12_1_4892 20 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 140 (accept_3_2 19 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 140 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 83 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 140 (accept_3_2 16 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 140 (accept_3_2 13 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 140
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 140 (accept_3_2 10 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 83 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 140 (accept_3_2 7 83 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 83 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 140
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 5 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 140 (accept_3_2 4 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 140 (accept_3_2 1 83 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 82 140 (Eq.refl
  Bool.true) (allA_of_3_0 59 82 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 81 140 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 140 (accept_3_2 58 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 140 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 140
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 140 (accept_3_2 55 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 140 (accept_3_2 52 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 140 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 140
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 50 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 140 (accept_3_2 49 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 140 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 140 (accept_3_2 46 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 140
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 44 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 140 (accept_3_2 43 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 140 (accept_3_2 40 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 140 (Polychromatic418967fa.accept_18_3_9_14_1_2219 39 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 140
  (Polychromatic418967fa.accept_21_17_18_14_1_4138 38 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 81 140 (accept_3_2 37 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 81 140 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 140 (accept_3_2 34 81 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 140 (Polychromatic418967fa.accept_13_7_3_10_1_656
  33 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 140
  (Polychromatic418967fa.accept_13_6_3_10_1_698 32 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 140 (accept_3_2 31 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 140 (accept_3_2 28 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 140 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 140
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 140 (accept_3_2 25 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 140 (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 140 (accept_3_2 22 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 140
  (Polychromatic418967fa.accept_13_7_3_10_1_656 20 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 140 (accept_3_2 19 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 140 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 140 (accept_3_2 16 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 140 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 140
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 140 (accept_3_2 13 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 140 (accept_3_2 10 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 140 (Polychromatic418967fa.accept_17_9_13_4_1_2408 9 81 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 140
  (Polychromatic418967fa.accept_16_8_1_12_1_984 8 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 140 (accept_3_2 7 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  140 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 140 (accept_3_2 4 81 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 140 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 81 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 140 (Polychromatic418967fa.accept_13_2_3_10_1_658 2
  81 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 140 (accept_3_2 1 81 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81 140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 80 140 (Eq.refl Bool.true) (allA_succ_of_gcd 60 80 140 20 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 140 (Polychromatic418967fa.accept_17_8_12_4_1_2525
  59 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 140 2 29 40 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 140 4 14 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 80 140 5 11 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 80 140 2 27 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 80 140 (Polychromatic418967fa.accept_17_2_12_4_1_5987 53 80 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 140 4 13 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 51
  80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 140 10 5 8 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 140 (accept_3_2 49
  80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 140 4 12 20 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 80 140 2 23 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 80 140 5 9 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 80 140 4 11 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 140 (accept_3_2 43 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  140 2 21 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 140 (Polychromatic418967fa.accept_17_7_12_4_1_2524 41 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 140 20 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 80 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 140 2 19 40 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 140 (accept_3_2 37 80 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 140 4 9 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 80 140 5 7 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 80 140 2 17 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 80 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 80 140 4 8 20 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 80 140 (accept_3_2 31 80 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80 140 10 3 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 80 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 80 140 4 7 20 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 80 140
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 80 140 2 13 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 80 140 5 5 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 80 140 4 6 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 80 140 (Polychromatic418967fa.accept_18_5_8_14_1_1282 23 80 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 140 2 11 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 140 20 1 4 7 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 140 (accept_3_2 19
  80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 140 2 9 40 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 80 140
  (Polychromatic418967fa.accept_11_6_3_8_1_843 17 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 80 140 4 4 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 80 140 5 3 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 80 140 2 7 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 140 (accept_3_2 13 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  140 4 3 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 80 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 140 10 1 8 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 140 (Polychromatic418967fa.accept_17_9_12_4_1_3468 9 80 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 140 4 2 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 140 (accept_3_2 7 80 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 140 2 3 40 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 80 140 5 1 16 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 80 140 4 1 20 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 80 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 80 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 140 2 1 40 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 140 (accept_3_2 1 80 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 80 140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 79 140 (Eq.refl Bool.true) (allA_of_3_0 62 79 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  63 78 140 (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 140 2 31 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 140 (accept_3_2 61 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 78 140 2 30 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 78 140 (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 140 2 29 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 140 2 28 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 78 140 (accept_3_2 55 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78
  140 2 27 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  78 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 78 140 2 26 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 78 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 51 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 140 2 25 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 140 (accept_3_2 49 78 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 140 2 24 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 78 140 2 23 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 78 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 140 2 22 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 140 (accept_3_2 43 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 140 2 21 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 140 (Polychromatic418967fa.accept_21_20_15_14_1_7234 41 78
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 140 2 20 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 140 2 19 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 140 (accept_3_2 37 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78
  140 2 18 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  78 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 78 140 2 17 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 78 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 140 2 16 39 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 140 (accept_3_2 31 78 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 140 2 15 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 78 140 2 14 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 78 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 140 2 13 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 140 (accept_3_2 25 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 140 2 12 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 140 (Polychromatic418967fa.accept_15_8_3_5_1_608 23 78 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 140 2 11 39 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 140 2 10 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 140 (accept_3_2 19 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78
  140 2 9 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  78 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 140 2 8 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 140 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 140 2 7 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 140 (accept_3_2 13 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 140 2 6 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 78 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 78 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 140 2 5 39 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 140 2 4 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 140 (accept_3_2 7 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 140
  2 3 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78
  140 (Polychromatic418967fa.accept_19_5_2_7_1_1019 5 78 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 140 2 2 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 140 2 1 39 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 140 (accept_3_2 1 78 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 78 140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 77
  140 (Eq.refl Bool.true) (allA_succ_of_gcd 63 77 140 7 9 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 77 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 140 (accept_3_2 61 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 140
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 77 140 (Polychromatic418967fa.accept_13_7_12_10_1_640 59 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 77 140 (accept_3_2 58 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 77 140 7 8 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 77 140 (accept_3_2 55 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 140 (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 140
  (Polychromatic418967fa.accept_17_2_9_4_1_3463 53 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 140 (accept_3_2 52 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 77 140 7 7 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 77 140 (Polychromatic418967fa.accept_13_9_12_10_1_242
  48 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 140
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 140 (accept_3_2 46 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 140 (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 140 (accept_3_2 43 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 77 140 7 6 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 77 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 77 140 (accept_3_2 40 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 77 140
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 77 140 (accept_3_2 37 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  77 140 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 77 140 7 5 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 77 140 (accept_3_2 34 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 77 140 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 77
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 140 (accept_3_2 31 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 140 (Polychromatic418967fa.accept_17_13_9_4_1_5979
  30 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 140
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 77 140 7 4 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 77 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 140 (accept_3_2 25 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 140
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 77 140 (Polychromatic418967fa.accept_19_4_1_7_1_4438 23 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 77 140 (accept_3_2 22 77 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 77 140 7 3 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 77 140 (Polychromatic418967fa.accept_13_7_12_10_1_640 20 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 140 (accept_3_2 19 77 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 140 (Polychromatic418967fa.accept_15_3_2_5_1_2980 18 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 140
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 140 (accept_3_2 16 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 77 140 7 2 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 77 140 (accept_3_2 13 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 77 140 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 140 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 77
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 77 140 (accept_3_2 10 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 77 140
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 77 140 7 1 11 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 77 140 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 77 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 140 (Polychromatic418967fa.accept_23_5_8_2_1_7233 5 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 77 140 (accept_3_2 4 77 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 77 140
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 77 140 (accept_3_2 1 77 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 77
  140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 76 140 (Eq.refl Bool.true)
  (allA_of_3_0 65 76 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 75 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 75 140 5 13 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 64 75 140 (accept_3_2 64 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  75 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 75 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 62 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 140 (accept_3_2 61 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 140 5 12 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 140 (accept_3_2 58 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 140
  (Polychromatic418967fa.accept_21_15_12_14_1_7232 57 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 75 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75 140 5 11 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 75 140
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 140 (accept_3_2 52 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 140 5 10 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 140 (accept_3_2 49 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 140 (Polychromatic418967fa.accept_17_14_7_4_1_3476 48 75
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 75 140 (accept_3_2 46 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75
  140 5 9 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  75 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 75 140 (accept_3_2 43 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 75 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 75 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75 140 5 8 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 75 140
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 75 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 140 (accept_3_2 37 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 75 140 (Polychromatic418967fa.accept_16_4_11_12_1_1775 36 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 140 5 7 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 140 (accept_3_2 34 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 140
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 140 (accept_3_2 31 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75
  140 5 6 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  75 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 75 140 (accept_3_2 28 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 75 140 (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75 140 5 5 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 75 140
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 140 (accept_3_2 22 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 140 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 140 5 4 15 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 140 (accept_3_2 19 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 75 140 (accept_3_2 16 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75
  140 5 3 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14
  75 140 (Polychromatic418967fa.accept_17_14_7_4_1_3476 14 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 75 140 (accept_3_2 13 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 75 140 (Polychromatic418967fa.accept_17_12_7_4_1_7231 12 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 75 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75 140 5 2 15 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 75 140
  (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 75 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 140 (accept_3_2 7 75 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 75 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 140 5 1 15 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 140 (accept_3_2 4 75 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 75 140 (Polychromatic418967fa.accept_17_3_7_4_1_7230 3 75 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 75 140 (accept_3_2 1 75 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 74 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 74 140 2 33 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 74 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 140 2 32 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 140 (Polychromatic418967fa.accept_29_5_16_24_1_7229
  63 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 140 2 31 37 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 140 (accept_3_2 61
  74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 140 2 30 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 59 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 74 140 2 29 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 74 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 140 2 28 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 140 (accept_3_2 55 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 140 2 27 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 74 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 74 140 2 26 37 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 74 140
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 74 140 2 25 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 74 140 (accept_3_2 49 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74
  140 2 24 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  74 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 74 140 2 23 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 74 140 (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 74 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 140 2 22 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 140 (accept_3_2 43 74 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 140 2 21 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 140
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 74 140 2 20 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 74 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 140 2 19 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 140 (accept_3_2 37 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 140 2 18 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 74 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 74 140 2 17 37 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 74 140
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 74 140 2 16 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 74 140 (accept_3_2 31 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74
  140 2 15 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  74 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 74 140 2 14 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 74 140 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 74 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 140 2 13 37 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 140 (accept_3_2 25 74 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 140 2 12 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 74 140 2 11 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 74 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 74 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 140 2 10 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 140 (accept_3_2 19 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 140 2 9 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 74 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 74 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 140 2 8 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 140
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 140 2 7 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 140 (accept_3_2 13 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  140 2 6 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 140 2 5 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 140 (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 140 2 4 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 140 (accept_3_2 7 74 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 140 2 3 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 74 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 140 2 2 37 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 140 2 1 37 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 140 (accept_3_2 1 74 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 73 140 (Eq.refl Bool.true)
  (allA_of_3_0 68 73 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 72 140 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 72 140 4 17 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 140 (accept_3_2 67 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72
  140 2 33 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  72 140 (Polychromatic418967fa.accept_16_1_8_12_1_405 65 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 72 140 4 16 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 72 140 (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 140 2 31 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 140 (accept_3_2 61 72 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 140 4 15 18 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 140
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 59 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 72 140 2 29 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 72 140 (Polychromatic418967fa.accept_16_9_8_12_1_979 57 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 140 4 14 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 140 (accept_3_2 55 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 140 2 27 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 140 (Polychromatic418967fa.accept_15_8_12_5_1_2987 53 72 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 140 4 13 18 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 140
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 51 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 140 2 25 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 140 (accept_3_2 49 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72
  140 4 12 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  72 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 72 140 2 23 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 72 140 (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 140 4 11 18 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 140 (accept_3_2 43 72 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 140 2 21 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 140
  (Polychromatic418967fa.accept_16_9_8_12_1_979 41 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 72 140 4 10 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 72 140 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 72 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 140 2 19 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 140 (accept_3_2 37 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 140 4 9 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 72 140 (Polychromatic418967fa.accept_16_3_8_12_1_2736 35 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 140 2 17 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 140
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 140 4 8 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 140 (accept_3_2 31 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  140 2 15 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 140 (Polychromatic418967fa.accept_13_3_7_10_1_668 29 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 140 4 7 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 140 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 140 2 13 36 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 140 (accept_3_2 25 72 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 140 4 6 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 140 (Polychromatic418967fa.accept_15_8_12_5_1_2987
  23 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 140 2 11 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 140
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 140 4 5 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 140 (accept_3_2 19 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  140 2 9 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 140 (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 140 4 4 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 140 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 140 2 7 36 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 140 (accept_3_2 13 72 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 140 4 3 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 140 (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 72
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 140 2 5 36 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 140
  (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 140 4 2 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 140 (accept_3_2 7 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 140
  2 3 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  140 (Polychromatic418967fa.accept_16_5_8_12_1_1766 5 72 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 72 140 4 1 18 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 72 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 140 2 1 36 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 140 (accept_3_2 1 72 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 72 140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  70 71 140 (Eq.refl Bool.true) (allA_succ_of_accept 69 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 71 140
  (Polychromatic418967fa.accept_11_2_5_8_1_470 68 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 71 140 (accept_3_2 67 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  71 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 71 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 140 (accept_3_2 64 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 140
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 140 (accept_3_2 61 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 140 (accept_3_2 58 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 140 (accept_3_2 55 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 140 (Polychromatic418967fa.accept_13_2_6_10_1_2703 54 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 140 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 140 (accept_3_2 52 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 140
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 140 (accept_3_2 49 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 140 (accept_3_2 46 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 140
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 44 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 140 (accept_3_2 43 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 140 (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 140 (accept_3_2 40 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 140 (accept_3_2 37 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 140 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 140 (accept_3_2 34 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 140
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 140 (accept_3_2 31 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 140 (accept_3_2 28 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 140
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 140 (accept_3_2 25 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 140 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 140 (accept_3_2 22 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 140 (accept_3_2 19 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 140 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 140 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 140 (accept_3_2 16 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 140
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 140 (accept_3_2 13 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 140 (accept_3_2 10 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 140
  (Polychromatic418967fa.accept_15_8_11_5_1_169 8 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 140 (accept_3_2 7 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  140 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 140 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 140 (accept_3_2 4 71 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  71 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 140 (accept_3_2 1 71 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 140 (allA_of_3_0 70 70 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 140 (allA_succ_of_accept 68 69 140
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 68 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 140 (accept_3_2 67 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 140 (accept_3_2 64 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 140 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 140 (accept_3_2 61 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 140 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 140 (accept_3_2 58 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 140 (accept_3_2 55 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 140 (accept_3_2 52 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 140 (Polychromatic418967fa.accept_21_9_6_14_1_7228 51 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 140
  (Polychromatic418967fa.accept_11_6_3_8_1_843 50 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 140 (accept_3_2 49 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 140 (accept_3_2 46 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 140 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 140 (accept_3_2 43 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 140 (accept_3_2 40 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 140 (accept_3_2 37 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 140 (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 140 (accept_3_2 34 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 140
  (Polychromatic418967fa.accept_13_6_4_10_1_660 32 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 140 (accept_3_2 31 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 140 (accept_3_2 28 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 140 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 140 (accept_3_2 25 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 140 (Polychromatic418967fa.accept_13_11_4_10_1_3440 24 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 140 (accept_3_2 22 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 140 (accept_3_2 19 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 140 (accept_3_2 16 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 140 (Polychromatic418967fa.accept_19_15_12_7_1_7227 15 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 140
  (Polychromatic418967fa.accept_13_1_4_10_1_622 14 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 140 (accept_3_2 13 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 140 (accept_3_2 10 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 69 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 140 (accept_3_2 7 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  140 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 140 (accept_3_2 4 69 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 69 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  69 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 140 (accept_3_2 1 69 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 140 (allA_succ_of_accept 67 68
  140 (accept_3_2 67 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 140 2 33 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 140
  (Polychromatic418967fa.accept_16_1_4_12_1_376 65 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 140 4 16 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 140 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 140 2 31 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 140 (accept_3_2 61 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 140 4 15 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 140 (Polychromatic418967fa.accept_13_7_3_10_1_656 59 68 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 140 2 29 34 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 140
  (Polychromatic418967fa.accept_15_12_8_5_1_5048 57 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 140 4 14 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 140 (accept_3_2 55 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  140 2 27 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 140 (Polychromatic418967fa.accept_16_5_4_12_1_3800 53 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 140 4 13 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 140 (Polychromatic418967fa.accept_16_3_4_12_1_3799 51 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 140 2 25 34 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 140 (accept_3_2 49 68 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 140 4 12 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 140
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 47 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 140 2 23 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 140 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 68 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 140 4 11 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 140 (accept_3_2 43 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 140 2 21 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 140 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 68 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 140 4 10 17 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 140
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 140 2 19 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 140 (accept_3_2 37 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  140 4 9 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 140 (Polychromatic418967fa.accept_16_3_4_12_1_3799 35 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 140 2 17 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 140 (Polychromatic418967fa.accept_13_7_3_10_1_656 33 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 140 4 8 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 140 (accept_3_2 31 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 140 2 15 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 140 (Polychromatic418967fa.accept_15_14_8_5_1_2104
  29 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 140 4 7 17 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 140
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 140 2 13 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 140 (accept_3_2 25 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  140 4 6 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 140 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 140 2 11 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 140 (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 140 4 5 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 140 (accept_3_2 19 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 140 2 9 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 140 (Polychromatic418967fa.accept_16_1_4_12_1_376 17 68 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 140 4 4 17 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 140
  (Polychromatic418967fa.accept_13_2_3_10_1_658 15 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 140 2 7 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 140 (accept_3_2 13 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  140 4 3 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 140 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 140 2 5 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 140 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 140 4 2 17 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 140 (accept_3_2 7 68 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 140 2 3 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 140 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 68 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 140 4 1 17 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 140
  (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 140 2 1 34 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 140 (accept_3_2 1 68 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 140 (allA_of_3_0 67 67 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 140 (allA_succ_of_accept 65 66 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 140 2 32 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 140 2 31 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 140 (accept_3_2 61 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 140 2 30 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 140 (Polychromatic418967fa.accept_15_14_6_5_1_7215 59 66 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 140 2 29 33 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 140 2 28 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 140 (accept_3_2 55 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  140 2 27 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 140 2 26 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 66 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 140 2 25 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 140 (accept_3_2 49 66 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 140 2 24 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 140 2 23 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 140 2 22 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 140 (accept_3_2 43 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 140 2 21 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 140 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 66 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 140 2 20 33 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 140
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 140 2 19 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 140 (accept_3_2 37 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  140 2 18 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 140 2 17 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 66 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 140 2 16 33 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 140 (accept_3_2 31 66 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 140 2 15 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 140 2 14 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 140 2 13 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 140 (accept_3_2 25 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 140 2 12 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 140 (Polychromatic418967fa.accept_16_7_2_12_1_1754 23 66 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 140 2 11 33 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 140 2 10 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 140 (accept_3_2 19 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  140 2 9 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 140 2 8 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 140 2 7 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 140 (accept_3_2 13 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 140 2 6 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 66 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 140 2 5 33 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 140 2 4 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 140 (accept_3_2 7 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 140
  2 3 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  140 (Polychromatic418967fa.accept_19_5_9_7_1_3137 5 66 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 66 140 2 2 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 66 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 140 2 1 33 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 140 (accept_3_2 1 66 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 66 140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65
  140 (allA_succ_of_accept 64 65 140 (accept_3_2 64 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 140 (accept_3_2 61 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 65 140 5 12 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 65 140 (Polychromatic418967fa.accept_16_11_1_12_1_1795 59 65
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 65 140 (accept_3_2 58 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 57
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 65 140
  (Polychromatic418967fa.accept_16_8_1_12_1_984 56 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 65 140 5 11 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 65 140 (Polychromatic418967fa.accept_19_16_8_7_1_7226 54 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 65 140 (accept_3_2 52 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 65 140 5 10 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 65 140 (accept_3_2 49
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 48 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 65 140 (Polychromatic418967fa.accept_17_13_14_4_1_2468 47 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 65 140 (accept_3_2 46 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 65 140 5 9 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 65 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 140 (accept_3_2 43 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 140
  (Polychromatic418967fa.accept_17_7_14_4_1_4745 41 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 65 140 5 8 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 65 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 140 (accept_3_2 37 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 140 (Polychromatic418967fa.accept_16_4_1_12_1_1792
  36 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 65 140 5 7 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 65 140 (accept_3_2 34
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 65 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 65 140 (Polychromatic418967fa.accept_21_11_2_14_1_7225 32 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 140 (accept_3_2 31 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 65 140 5 6 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 65 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 65 140 (accept_3_2 28 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 65 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 65 140 5 5 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 65 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 140 (Polychromatic418967fa.accept_18_5_11_14_1_7203 23 65
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 65 140 (accept_3_2 22 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 65 140 5 4 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 65 140 (accept_3_2 19
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 140
  (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 65 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 65 140 (accept_3_2 16 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 65 140 5 3 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 65 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 140 (accept_3_2 13 65 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 65 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 140
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 65 140 5 2 13 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 65 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 140 (accept_3_2 7 65 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 65 140 5 1 13 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 65 140 (accept_3_2 4 65
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65 140 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 65 140
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 65 140 (accept_3_2 1 65 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 65
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 140 (allA_of_3_0 64 64 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 63 140 (allA_succ_of_accept 62 63 140
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 62 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 140 (accept_3_2 61 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 140 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 140 (accept_3_2 58 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 140 (Polychromatic418967fa.accept_18_3_9_14_1_2219 57 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 63 140 7 8 9 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 63 140 (accept_3_2 55 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 63 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 63 140 (accept_3_2 52 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  63 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 63 140 (Polychromatic418967fa.accept_16_2_15_12_1_1744 50 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 63 140 7 7 9 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 63 140
  (Polychromatic418967fa.accept_25_23_13_15_1_7224 48 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 140 (accept_3_2 46 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 140 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 140
  (Polychromatic418967fa.accept_25_19_13_15_1_5391 44 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 63 140 (accept_3_2 43 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 63 140 7 6 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 140 (accept_3_2 40 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 63 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 140
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 38 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 63 140 (accept_3_2 37 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 63 140 (Polychromatic418967fa.accept_15_6_3_5_1_607 36 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 63 140 7 5 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 63 140 (accept_3_2 34 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 63 140 (Polychromatic418967fa.accept_19_14_6_7_1_7223 33 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 140
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 140 (accept_3_2 31 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 63 140 7 4 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 63 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 27
  63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 140
  (Polychromatic418967fa.accept_17_9_12_4_1_3468 26 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 140 (accept_3_2 25 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 140 (accept_3_2 22 63 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 140 7 3 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 63 140 (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 140 (accept_3_2 19 63 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 63 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 63 140 (accept_3_2 16 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  63 140 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 63 140 7 2 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 63 140 (accept_3_2 13 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 63 140 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 140 (accept_3_2 10 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9
  63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 140
  (Polychromatic418967fa.accept_13_8_11_10_1_636 8 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 63 140 7 1 9 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 63 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 140 (accept_3_2 4 63 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 140
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 140 (accept_3_2 1 63 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 140 (allA_succ_of_accept 61 62 140
  (accept_3_2 61 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 140 2 30 31 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 140
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 140 2 29 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 140 2 28 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 140 (accept_3_2 55 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 140 2 27 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 62 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 140 2 26 31 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 140 2 25 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 140 (accept_3_2 49 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  140 2 24 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 140 2 23 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 140 (Polychromatic418967fa.accept_22_1_18_8_1_5619 45 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 140 2 22 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 140 (accept_3_2 43 62 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 140 2 21 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 140
  (Polychromatic418967fa.accept_12_5_2_8_1_172 41 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 140 2 20 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 140 2 19 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 140 (accept_3_2 37 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 140 2 18 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 140 2 17 31 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 140 2 16 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 140 (accept_3_2 31 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  140 2 15 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 140 2 14 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 140 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 140 2 13 31 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 140 (accept_3_2 25 62 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 140 2 12 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 140 2 11 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 62 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 140 2 10 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 140 (accept_3_2 19 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 140 2 9 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 140 2 8 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 140 2 7 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 140 (accept_3_2 13 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  140 2 6 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 140 2 5 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 140 (Polychromatic418967fa.accept_19_9_5_7_1_5853 9 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 140 2 4 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 140 (accept_3_2 7 62 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 140 2 3 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 62 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 140 2 2 31 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 140 2 1 31 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 140 (accept_3_2 1 62 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 140 (allA_of_3_0 61 61 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 140 (allA_succ_of_accept 59 60 140
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 59 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 140 2 29 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 140 4 14 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 60 140 5 11 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 60 140 2 27 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 53
  60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 140 4 13 15 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 140
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 140 10 5 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 140 (accept_3_2 49 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  140 4 12 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 140 2 23 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 140 5 9 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 140 4 11 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 60 140 (accept_3_2 43 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 140 2 21 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 140 (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60 140 20 2 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 60 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 60 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 140 2 19 30 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 140 (accept_3_2 37
  60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 140 4 9 15 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 60 140 5 7 12 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 60 140 2 17 30 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 140
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 140 4 8 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 140 (accept_3_2 31 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  140 10 3 6 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 140 4 7 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 140 (Polychromatic418967fa.accept_18_9_6_14_1_5913 27 60 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 140 2 13 30 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 60 140 5 5 12 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 60 140 4 6 15 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 140
  (Polychromatic418967fa.accept_19_4_3_7_1_5876 23 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 140 2 11 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 140 20 1 3 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 140 (accept_3_2 19 60 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 60 140 2 9 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 60 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 60 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 140 4 4 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 60 140 5 3 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 60 140 2 7 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 140 (accept_3_2 13 60 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 140 4 3 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 60 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 60 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 140 10 1 6 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 140
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 140 4 2 15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 140 (accept_3_2 7 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 140
  2 3 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 60 140 5
  1 12 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 60 140 4 1
  15 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 140 2 1 30 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 140 (accept_3_2 1 60 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 140 (allA_succ_of_accept 58 59 140
  (accept_3_2 58 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 140 (accept_3_2 55 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 140 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 140
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 53 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 140 (accept_3_2 52 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 140 (accept_3_2 49 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 140 (Polychromatic418967fa.accept_22_4_15_8_1_7222 48 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 140
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 140 (accept_3_2 46 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 140 (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 140 (accept_3_2 43 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 140 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 59 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 140
  (Polychromatic418967fa.accept_17_7_8_4_1_1520 41 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 140 (accept_3_2 40 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 140 (accept_3_2 37 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 140 (Polychromatic418967fa.accept_15_6_14_5_1_2976 36 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 140
  (Polychromatic418967fa.accept_17_1_8_4_1_1519 35 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 140 (accept_3_2 34 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 140 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 140 (accept_3_2 31 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 140 (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 59
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 140
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 140 (accept_3_2 28 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 140 (accept_3_2 25 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 140 (Polychromatic418967fa.accept_15_9_14_5_1_2086 24 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 140
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 140 (accept_3_2 22 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 140 (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 140 (accept_3_2 19 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 140 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 59 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 140
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 140 (accept_3_2 16 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 140 (accept_3_2 13 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 140
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 140 (accept_3_2 10 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 140 (Polychromatic418967fa.accept_13_8_7_10_1_4362 8 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 140 (accept_3_2 7 59 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 140 (Polychromatic418967fa.accept_15_6_14_5_1_2976 6 59 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 140
  (Polychromatic418967fa.accept_19_5_2_7_1_1019 5 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 140 (accept_3_2 4 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 140 (accept_3_2 1 59 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 140 (allA_of_3_0
  58 58 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 140 (allA_succ_of_accept 56 57 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 140 (accept_3_2 55 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 140 (accept_3_2 52 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 140
  (Polychromatic418967fa.accept_16_2_9_12_1_46 50 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 140 (accept_3_2 49 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 140 (Polychromatic418967fa.accept_18_12_3_14_1_5919 48 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 140 (accept_3_2 46 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 140 (accept_3_2 43 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 140 (accept_3_2 40 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 140 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 140 (accept_3_2 37 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 140 (Polychromatic418967fa.accept_15_6_12_5_1_2108 36 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 140 (accept_3_2 34 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 140
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 32 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 140 (accept_3_2 31 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 140 (accept_3_2 28 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 140 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 140 (accept_3_2 25 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 140 (accept_3_2 22 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 140 (accept_3_2 19 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 140 (accept_3_2 16 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 140
  (Polychromatic418967fa.accept_23_14_11_2_1_7221 14 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 140 (accept_3_2 13 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 140 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 140 (accept_3_2 10 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 140 (Polychromatic418967fa.accept_15_9_12_5_1_1267 9 57 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 140 (accept_3_2 7 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 57 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 140 (accept_3_2 4 57 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 140 (Polychromatic418967fa.accept_16_3_9_12_1_4831 3 57 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 57
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 140 (accept_3_2 1 57 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 140)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 140 (allA_succ_of_accept 55 56 140 (accept_3_2 55 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 140 2 27 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 56 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 140 4 13 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 51
  56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 140 2 25 28 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 56 140 7 7 8 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 56 140 4 12 14 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 140
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 140 2 23 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 140 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 56 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 140 4 11 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 140 (accept_3_2 43 56 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 140 14 3 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 56 140 (Polychromatic418967fa.accept_16_9_8_12_1_979 41 56 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 140 4 10 14 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 140 2 19 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 140 (accept_3_2 37 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  140 4 9 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 56
  140 7 5 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 56
  140 2 17 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  56 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 56 140 4 8 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 140 (accept_3_2 31 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 140 2 15 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 56 140 (Polychromatic418967fa.accept_16_13_8_12_1_2723 29 56 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 140 28 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 140 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 56 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 140 2 13 28 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 140 (accept_3_2 25
  56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 140 4 6 14 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 140
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 140 2 11 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 56 140 7 3 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 56 140 4 5 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 140 (accept_3_2 19 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  140 2 9 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 140 4 4 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 56 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 140 14 1 4 10 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 140 (accept_3_2 13 56 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 140 4 3 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 56 140 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 56 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 140 2 5 28 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 140
  (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 56 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 140 4 2 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 56 140 7 1 8 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 56 140 2 3 28 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 56 140 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 56 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 140 4 1 14 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 56 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 140 2 1 28 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 140 (accept_3_2 1 56 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56 140))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 55 140 (allA_of_3_0 55 55 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 140
  (allA_succ_of_accept 53 54 140 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 54 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 140 2 26 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 51
  54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 140 2 25 27 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 140 (accept_3_2 49
  54 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 140 2 24 27 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 140
  (Polychromatic418967fa.accept_13_8_2_10_1_652 47 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 54 140 2 23 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 54 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 140 2 22 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 140 (accept_3_2 43 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 140 2 21 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 140 (Polychromatic418967fa.accept_15_11_9_5_1_2974 41 54 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 140 2 20 27 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 140
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 54 140 2 19 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 54 140 (accept_3_2 37 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54
  140 2 18 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  54 140 (Polychromatic418967fa.accept_25_10_4_15_1_7220 35 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 54 140 2 17 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 54 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 140 2 16 27 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 140 (accept_3_2 31 54 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 140 2 15 27 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 140
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 54 140 2 14 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 54 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 54 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 140 2 13 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 140 (accept_3_2 25 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 140 2 12 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 140 (Polychromatic418967fa.accept_19_4_16_7_1_5870 23 54 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 140 2 11 27 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 54 140 2 10 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 54 140 (accept_3_2 19 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54
  140 2 9 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  54 140 (Polychromatic418967fa.accept_19_17_16_7_1_7213 17 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 54 140 2 8 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 54 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 140 2 7 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 140 (accept_3_2 13 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 140 2 6 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 54 140 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 54 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 140 2 5 27 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 54 140
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 54 140 2 4 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 54 140 (accept_3_2 7 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 140
  2 3 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54
  140 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 54 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 54 140 2 2 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 54 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 140 2 1 27 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 140 (accept_3_2 1 54 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 54 140)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 140
  (allA_succ_of_accept 52 53 140 (accept_3_2 52 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 53 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 140 (accept_3_2 49 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 53 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 53 140 (accept_3_2 46 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 53 140 (Polychromatic418967fa.accept_15_14_8_5_1_2104 44 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 140 (accept_3_2 43 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 53 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 53 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 140
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 53 140 (accept_3_2 40 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 53 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 140 (accept_3_2 37 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 140 (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 140
  (Polychromatic418967fa.accept_13_9_1_10_1_647 35 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 140 (accept_3_2 34 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 140 (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 140 (accept_3_2 31 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 53 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 140 (accept_3_2 28 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 140 (accept_3_2 25 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 140
  (Polychromatic418967fa.accept_16_7_5_12_1_4824 23 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 140 (accept_3_2 22 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 140 (accept_3_2 19 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 140 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 140
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 140 (accept_3_2 16 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 140 (accept_3_2 13 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 140 (accept_3_2 10 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 140 (Polychromatic418967fa.accept_16_8_5_12_1_3812 8 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 140 (accept_3_2 7 53 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 53 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 140
  (Polychromatic418967fa.accept_21_5_11_14_1_7219 5 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 140 (accept_3_2 4 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 140 (accept_3_2 1 53 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 140))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 140 (allA_of_3_0 52 52
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 140 (allA_succ_of_accept 50 51 140
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 51 140 (accept_3_2 49 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 51 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 51 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 140 (accept_3_2 46 51 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 140 (Polychromatic418967fa.accept_13_6_12_10_1_690
  45 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 140 (accept_3_2 43 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 140 (accept_3_2 40 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 140 (accept_3_2 37 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 140 (Polychromatic418967fa.accept_16_4_3_12_1_4892 36 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 140 (accept_3_2 34 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 140 (Polychromatic418967fa.accept_13_7_12_10_1_640 33 51 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 140
  (Polychromatic418967fa.accept_13_6_12_10_1_690 32 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 140 (accept_3_2 31 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 140 (accept_3_2 28 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 140 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 51 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 140 (accept_3_2 25 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 140 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 140 (accept_3_2 22 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 51 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 140 (accept_3_2 19 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 140 (accept_3_2 16 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 140
  (Polychromatic418967fa.accept_15_14_6_5_1_7215 14 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 140 (accept_3_2 13 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 140 (accept_3_2 10 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 140 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 51 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 140 (accept_3_2 7 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 140 (accept_3_2 4 51 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 51 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  51 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 140 (accept_3_2 1 51 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 140)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 140 (allA_succ_of_accept 49 50 140 (accept_3_2 49 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 140 2 24 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 140 2 23 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 50 140 5 9 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 50 140 2 22 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 140 (accept_3_2 43 50 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 140 2 21 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 140 10 4 5 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 140
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 140 2 19 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 140 (accept_3_2 37 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  140 2 18 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 50
  140 5 7 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 50
  140 2 17 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  50 140 (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 50 140 2 16 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 50 140 (accept_3_2 31 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 50 140 10 3 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 50 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 50 140 2 14 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 50 140 (Polychromatic418967fa.accept_13_1_11_10_1_1258
  27 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 140 2 13 25 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 50 140 5 5 10 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 50 140 2 12 25 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 140
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 140 2 11 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 140 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 140 10 2 5 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 140 (accept_3_2 19 50 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 50 140 2 9 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 50 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 50 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 140 2 8 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 50 140 5 3 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 50 140 2 7 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 140 (accept_3_2 13 50 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 140 2 6 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 50 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 50 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 140 10 1 5 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 140
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 140 2 4 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 140 (accept_3_2 7 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 140
  2 3 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 50 140 5
  1 10 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 50 140 2 2
  25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 140
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 140 2 1 25 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 140 (accept_3_2 1 50 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  140)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 140 (allA_of_3_0 49 49 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 140 (allA_succ_of_accept 47 48 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 48
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 140 2 23 24 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 140
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 140 4 11 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 140 (accept_3_2 43 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  140 2 21 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 140 (Polychromatic418967fa.accept_17_7_14_4_1_4745 41 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 140 4 10 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 39 48 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 140 2 19 24 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 140 (accept_3_2 37 48 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 140 4 9 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 35
  48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48 140 2 17 24 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 48 140
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 48 140 4 8 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 140 (accept_3_2 31 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48
  140 2 15 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  48 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 48 140 4 7 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 48 140 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 48 140 2 13 24 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 140 (accept_3_2 25 48 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 140 4 6 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 48 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 140 2 11 24 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 140
  (Polychromatic418967fa.accept_15_6_3_5_1_607 21 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 48 140 4 5 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 48 140 (accept_3_2 19 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48
  140 2 9 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  48 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 48 140 4 4 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 48 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 48 140 2 7 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 48 140 (accept_3_2 13 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 140 4 3 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 48 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 48 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 140 2 5 24 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 140
  (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 48 140 4 2 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 48 140 (accept_3_2 7 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 140
  2 3 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 48
  140 (Polychromatic418967fa.accept_19_5_10_7_1_5887 5 48 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 48 140 4 1 12 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 48 140 (Polychromatic418967fa.accept_18_3_12_14_1_2232 3 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 48 140 2 1 24 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 140 (accept_3_2 1 48 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 48 140)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 140
  (allA_succ_of_accept 46 47 140 (accept_3_2 46 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 47 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 140 (accept_3_2 43 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 47 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 140
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 47 140 (accept_3_2 40 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 47 140 (Polychromatic418967fa.accept_11_5_3_8_1_454 38 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 140 (accept_3_2 37 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 47 140 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 140
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 47 140 (accept_3_2 34 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 47 140 (Polychromatic418967fa.accept_19_13_9_7_1_2038 32 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 140 (accept_3_2 31 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 47 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 47 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 140
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 29 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 47 140 (accept_3_2 28 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 47 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 140 (accept_3_2 25 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 47 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 140
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 23 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 47 140 (accept_3_2 22 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 47 140 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 140 (accept_3_2 19 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 47 140 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 47
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 140
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 140 (accept_3_2 16 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 140 (accept_3_2 13 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 140
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 140 (accept_3_2 10 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 140 (accept_3_2 7 47 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 47 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 140
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 140 (accept_3_2 4 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 140 (accept_3_2 1 47 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 140))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 140 (allA_of_3_0 46 46 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 45 140 (allA_succ_of_accept 44 45 140
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 44 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 140 (accept_3_2 43 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  45 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 45 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45 140 5 8 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 45 140 (Polychromatic418967fa.accept_18_3_9_14_1_2219
  39 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 140
  (Polychromatic418967fa.accept_13_12_6_10_1_667 38 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 140 (accept_3_2 37 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  45 140 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 45 140 5 7 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 45 140 (accept_3_2 34 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 140 (Polychromatic418967fa.accept_17_15_11_4_1_7218 32 45
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 140 (accept_3_2 31 45 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 140 5 6 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 140 (accept_3_2 28 45
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 140
  (Polychromatic418967fa.accept_17_10_11_4_1_2522 27 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 140 (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 45 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45 140 5 5 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 45 140 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 45
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 140 (accept_3_2 22 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 140 (Polychromatic418967fa.accept_18_3_9_14_1_2219 21 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 45 140 5 4 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 45 140 (accept_3_2 19 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 45 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 140 (accept_3_2 16 45 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 140 5 3 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 140 (Polychromatic418967fa.accept_22_14_1_8_1_7217
  14 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 140 (accept_3_2 13
  45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 140
  (Polychromatic418967fa.accept_13_12_6_10_1_667 12 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45 140 5 2 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 140
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 8 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 140 (accept_3_2 7 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  140 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 45 140 5 1 9 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 45 140 (accept_3_2 4 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45
  140 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 45 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 45 140 (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 140 (accept_3_2 1 45 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 45 140))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 140
  (allA_succ_of_accept 43 44 140 (accept_3_2 43 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44
  140 2 21 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  44 140 (Polychromatic418967fa.accept_13_2_5_10_1_250 41 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 140 4 10 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 140 2 19 22 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 140 (accept_3_2 37 44 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 140 4 9 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 140 (Polychromatic418967fa.accept_19_16_6_7_1_4425
  35 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 140 2 17 22 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 140 4 8 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 140 (accept_3_2 31 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  140 2 15 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 140 4 7 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 140 (Polychromatic418967fa.accept_19_8_6_7_1_7216 27 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 140 2 13 22 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 140 (accept_3_2 25 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 140 4 6 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 140 (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 44 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 140 2 11 22 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 140 4 5 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 140 (accept_3_2 19 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  140 2 9 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 140 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 140 4 4 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 140 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 140 2 7 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 140 (accept_3_2 13 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 140 4 3 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 44 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 140 2 5 22 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 140
  (Polychromatic418967fa.accept_15_9_14_5_1_2086 9 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 140 4 2 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 140 (accept_3_2 7 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 140
  2 3 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  140 (Polychromatic418967fa.accept_18_5_8_14_1_1282 5 44 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 44 140 4 1 11 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 44 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 140 2 1 22 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 140 (accept_3_2 1 44 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 44 140)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 140 (allA_of_3_0 43 43
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 140 (allA_succ_of_accept 41 42 140
  (Polychromatic418967fa.accept_13_2_3_10_1_658 41 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 140 2 20 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 140 2 19 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 140 (accept_3_2 37 42 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 140 2 18 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 42 140 7 5 6 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 42 140 2 17 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 140 2 16 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 140 (accept_3_2 31
  42 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 140 2 15 21 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 140 14 2 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 42 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 140 2 13 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 140 (accept_3_2 25 42 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 140 2 12 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 140 (Polychromatic418967fa.accept_15_8_12_5_1_2987 23 42 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 140 2 11 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 140 7 3 6 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 140 2 10 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 140 (accept_3_2 19
  42 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 140 2 9 21 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 42 140 2 8 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 42 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 140 14 1 3 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 140 (accept_3_2 13 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 42 140 2 6 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 42 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 42 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 140 2 5 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 9
  42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 140 2 4 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 42 140 7 1 6 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 42 140 2 3 21 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 140
  (Polychromatic418967fa.accept_16_5_10_12_1_4904 5 42 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 42 140 2 2 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 42 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 140 2 1 21 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 140 (accept_3_2 1 42 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 42 140)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 140 (allA_succ_of_accept 40 41
  140 (accept_3_2 40 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 140 (accept_3_2 37 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 140 (Polychromatic418967fa.accept_15_6_11_5_1_168 36 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 140 (Polychromatic418967fa.accept_16_3_9_12_1_4831
  35 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 140 (accept_3_2 34
  41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 41 140 (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 140 (accept_3_2 31 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 41 140 (Polychromatic418967fa.accept_21_9_20_14_1_4139 30 41 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 140
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 140 (accept_3_2 28 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 140 (accept_3_2 25 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 140 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 41 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 140
  (Polychromatic418967fa.accept_15_8_11_5_1_169 23 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 140 (accept_3_2 22 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 140 (Polychromatic418967fa.accept_16_4_9_12_1_4829 20 41 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 140 (accept_3_2 19 41 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 140 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 41 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 140
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 140 (accept_3_2 16 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 140 (accept_3_2 13 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 140 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 41 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 140
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 140 (accept_3_2 10 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 140 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 140 (accept_3_2 7 41 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 140 (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 41 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 140
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 140 (accept_3_2 4 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 140 (accept_3_2 1 41 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 140))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 140 (allA_of_3_0 40 40 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 140 (allA_succ_of_accept 38 39 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 140 (accept_3_2 37 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 140 (accept_3_2 34 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 39 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 140
  (Polychromatic418967fa.accept_19_13_1_7_1_5906 32 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 140 (accept_3_2 31 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 140 (accept_3_2 28 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 140 (accept_3_2 25 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 140 (accept_3_2 22 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 140 (Polychromatic418967fa.accept_16_5_7_12_1_7206 21 39 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 140 (accept_3_2 19 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 140 (accept_3_2 16 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 39 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 140
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 140 (accept_3_2 13 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 140 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 140 (accept_3_2 10 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 140 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 39 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 140 (accept_3_2 7 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 39 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 140 (accept_3_2 4 39 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 140 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 39
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 140 (accept_3_2 1 39 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 140))))))))))))))))))))))))))))))))))))))) (allB_succ 38 140
  (allA_succ_of_accept 37 38 140 (accept_3_2 37 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  140 2 18 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 140 2 17 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 38 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 140 2 16 19 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 140 (accept_3_2 31 38 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 140 2 15 19 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 140
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 140 2 14 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 140 (Polychromatic418967fa.accept_15_12_8_5_1_5048 27 38 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 140 2 13 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 140 (accept_3_2 25 38 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 140 2 12 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 38 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 140 2 11 19 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 140 2 10 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 140 (accept_3_2 19 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  140 2 9 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 140 2 8 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 38 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 140 2 7 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 140 (accept_3_2 13 38 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 140 2 6 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 140 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 140 2 5 19 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 140
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 140 2 4 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 140 (accept_3_2 7 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 140
  2 3 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 38 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 140 2 2 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 38 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 140 2 1 19 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 140 (accept_3_2 1 38 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 140)))))))))))))))))))))))))))))))))))))) (allB_succ 37 140 (allA_of_3_0 37 37 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 140 (allA_succ_of_accept 35 36 140
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 35 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 140 2 17 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 140 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 36 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 140 4 8 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 140 (accept_3_2 31 36 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 140 2 15 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 140 (Polychromatic418967fa.accept_15_14_6_5_1_7215 29 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 140 4 7 9 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 140
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 140 2 13 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 140 (accept_3_2 25 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  140 4 6 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 140 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 140 2 11 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 140 (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 140 4 5 9 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 140 (accept_3_2 19 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 140 2 9 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 140 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 36 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 140 4 4 9 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 140
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 140 2 7 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 140 (accept_3_2 13 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  140 4 3 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 140 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 140 2 5 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 140 (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 36 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 140 4 2 9 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 140 (accept_3_2 7 36 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 140 2 3 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 140 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 36 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 140 4 1 9 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 140
  (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 140 2 1 18 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 140 (accept_3_2 1 36 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  140)))))))))))))))))))))))))))))))))))) (allB_succ 35 140 (allA_succ_of_accept 34 35 140 (accept_3_2 34 35 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 140
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 32 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 140 (accept_3_2 31 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 35
  140 5 6 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  35 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 35 140 7 4 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 35 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 140 (Polychromatic418967fa.accept_12_2_11_8_1_504
  26 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 35 140 5 5 7 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 35 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 35 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 140 (accept_3_2 22 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 35 140 7 3 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 35 140 5 4 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 35 140 (accept_3_2 19 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 35 140 (Polychromatic418967fa.accept_29_18_6_24_1_7214 18 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 140 (Polychromatic418967fa.accept_19_17_16_7_1_7213 17 35
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 140 (accept_3_2 16 35 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 35 140 5 3 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 35 140 7 2 5 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 35 140 (accept_3_2 13 35 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 35 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 140
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 35 140 5 2 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 35 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 140 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 35 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 35 140 7 1 5 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 35 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 35 140 5 1 7 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 35 140 (accept_3_2 4 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 140 (accept_3_2 1 35 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 140))))))))))))))))))))))))))))))))))) (allB_succ 34 140 (allA_of_3_0 34 34 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 33 140 (allA_succ_of_accept 32 33 140
  (Polychromatic418967fa.accept_15_2_3_5_1_2991 32 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 140 (accept_3_2 31 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 140 (accept_3_2 28 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 140 (Polychromatic418967fa.accept_16_11_1_12_1_1795 27 33 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 140 (accept_3_2 25 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 140 (accept_3_2 22 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 140
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 140 (accept_3_2 19 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 140 (accept_3_2 16 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 140 (Polychromatic418967fa.accept_17_15_16_4_1_2418 15 33 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 140
  (Polychromatic418967fa.accept_22_14_11_8_1_7212 14 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 140 (accept_3_2 13 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 140 (accept_3_2 10 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 140 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 33 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 140 (accept_3_2 7 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  140 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 140 (accept_3_2 4 33 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 33 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2
  33 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 140 (accept_3_2 1 33 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 140))))))))))))))))))))))))))))))))) (allB_succ 32 140
  (allA_succ_of_accept 31 32 140 (accept_3_2 31 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  140 2 15 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 140 (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 140 4 7 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 140 (Polychromatic418967fa.accept_15_12_2_5_1_3939 27 32 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 140 2 13 16 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 140 (accept_3_2 25 32 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 140 4 6 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 140 (Polychromatic418967fa.accept_19_4_13_7_1_4433 23 32 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 140 2 11 16 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 140
  (Polychromatic418967fa.accept_19_2_13_7_1_7211 21 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 140 4 5 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 140 (accept_3_2 19 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  140 2 9 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 140 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 140 4 4 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 140 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 32 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 140 2 7 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 140 (accept_3_2 13 32 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 140 4 3 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 140 (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 32 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 140 2 5 16 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 140
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 140 4 2 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 140 (accept_3_2 7 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 140
  2 3 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  140 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 32 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 140 4 1 8 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 140 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 32 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 140 2 1 16 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 140 (accept_3_2 1 32 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 140)))))))))))))))))))))))))))))))) (allB_succ 31 140 (allA_of_3_0 31 31 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 140 (allA_succ_of_accept 29 30 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 140 2 14 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 30 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 140 2 13 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 30 140 5 5 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 30 140 2 12 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 140 (Polychromatic418967fa.accept_19_4_11_7_1_7210
  23 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 140 2 11 15 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 140
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 140 10 2 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 140 (accept_3_2 19 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  140 2 9 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 140 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 140 2 8 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 30 140 5 3 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 30 140 2 7 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 30 140 (accept_3_2 13 30 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 140 2 6 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 30 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 140 10 1 3 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 30 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 140 2 4 15 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 140 (accept_3_2 7 30 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 140 2 3 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 30 140 5 1 6 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 30 140 2 2 15 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  30 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 140 2 1 15 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 140 (accept_3_2 1 30
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 140)))))))))))))))))))))))))))))) (allB_succ 29 140
  (allA_succ_of_accept 28 29 140 (accept_3_2 28 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  29 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 29 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 140 (accept_3_2 25 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 29 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 29 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 140
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 140 (accept_3_2 22 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 140 (Polychromatic418967fa.accept_13_7_3_10_1_656 20 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 140 (accept_3_2 19 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 140 (Polychromatic418967fa.accept_19_18_10_7_1_3174 18 29 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 140
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 140 (accept_3_2 16 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 140 (accept_3_2 13 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 140 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 29 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 140
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 140 (accept_3_2 10 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 140 (accept_3_2 7 29 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 29 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 140
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 5 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 140 (accept_3_2 4 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 140 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 140 (accept_3_2 1 29 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 140))))))))))))))))))))))))))))) (allB_succ 28 140 (allA_of_3_0 28 28 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 140 (allA_succ_of_accept 26 27 140 (Polychromatic418967fa.accept_16_10_11_12_1_4835
  26 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 140 (accept_3_2 25
  27 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 140
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 140 (accept_3_2 22 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 140 (Polychromatic418967fa.accept_15_6_12_5_1_2108 21 27 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 140
  (Polychromatic418967fa.accept_16_4_11_12_1_1775 20 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 27 140 (accept_3_2 19 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  27 140 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 27 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 140 (accept_3_2 16 27 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 140 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 140
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 140 (accept_3_2 13 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  27 140 (Polychromatic418967fa.accept_19_12_8_7_1_7209 12 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 27 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 140 (accept_3_2 10 27 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 140 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 27 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 140
  (Polychromatic418967fa.accept_15_8_12_5_1_2987 8 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 140 (accept_3_2 7 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 27 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 140 (accept_3_2 4 27 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 27 140 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 27 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 140 (Polychromatic418967fa.accept_11_2_5_8_1_470 2
  27 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 140 (accept_3_2 1 27 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 140))))))))))))))))))))))))))) (allB_succ 26 140
  (allA_succ_of_accept 25 26 140 (accept_3_2 25 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26
  140 2 12 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  26 140 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 26 140 2 11 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 26 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 26 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 140 2 10 13 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 140 (accept_3_2 19 26 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 140 2 9 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 26 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 140 2 8 13 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 140
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 140 2 7 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 140 (accept_3_2 13 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  140 2 6 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 140 2 5 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 140 (Polychromatic418967fa.accept_15_9_11_5_1_1283 9 26 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 140 2 4 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 140 (accept_3_2 7 26 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 140 2 3 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 140 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 26 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 140 2 2 13 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 140
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 140 2 1 13 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 140 (accept_3_2 1 26 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  140)))))))))))))))))))))))))) (allB_succ 25 140 (allA_of_3_0 25 25 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 24 140 (allA_succ_of_accept 23 24 140 (Polychromatic418967fa.accept_16_7_8_12_1_4902 23 24 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 140 2 11 12 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 140 4 5 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 140 (accept_3_2 19 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  140 2 9 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 140 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 140 4 4 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 140 (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 24 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 140 2 7 12 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 140 (accept_3_2 13 24 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 140 4 3 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 24 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 140 2 5 12 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 140
  (Polychromatic418967fa.accept_16_9_8_12_1_979 9 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 140 4 2 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 140 (accept_3_2 7 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 140
  2 3 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  140 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 24 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 140 4 1 6 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 24 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 140 2 1 12 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 140 (accept_3_2 1 24 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 140)))))))))))))))))))))))) (allB_succ 23 140 (allA_succ_of_accept 22 23 140 (accept_3_2 22
  23 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 140 (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 140 (accept_3_2 19 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 140 (Polychromatic418967fa.accept_15_3_8_5_1_2105 18 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 140
  (Polychromatic418967fa.accept_21_17_2_14_1_7208 17 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 140 (accept_3_2 16 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 140 (accept_3_2 13 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 140 (Polychromatic418967fa.accept_15_12_8_5_1_5048 12 23 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 140
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 140 (accept_3_2 10 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 140 (Polychromatic418967fa.accept_16_8_7_12_1_7207 8 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 140 (accept_3_2 7 23 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 140 (Polychromatic418967fa.accept_21_6_2_14_1_5688 6 23 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 140
  (Polychromatic418967fa.accept_16_5_7_12_1_7206 5 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 140 (accept_3_2 4 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 140 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 140 (accept_3_2 1 23 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 140))))))))))))))))))))))) (allB_succ 22 140 (allA_of_3_0 22 22 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 140 (allA_succ_of_accept 20 21 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 21
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 140 (accept_3_2 19 21 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 140 (Polychromatic418967fa.accept_12_6_9_8_1_165
  18 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 140
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 140 (accept_3_2 16 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  21 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 21 140 7 2 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 21 140 (accept_3_2 13 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 21 140 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 21 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 140 (accept_3_2 10 21 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 140 (Polychromatic418967fa.accept_8_1_5_4_1_388 9
  21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 140
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 21 140 7 1 3 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 21 140 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 21 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 140 (accept_3_2 4 21 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 140 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3
  21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 21 140 (accept_3_2 1 21 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21
  140))))))))))))))))))))) (allB_succ 20 140 (allA_succ_of_accept 19 20 140 (accept_3_2 19 20 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 140 2 9 10 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 20 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 20 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 20 140 4 4 5 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 20 140 5 3 4 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 20 140 2 7 10 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 140 (accept_3_2 13 20 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 140 4 3 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 140 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 20
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 140 10 1 2 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 140
  (Polychromatic418967fa.accept_16_9_4_12_1_4896 9 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 140 4 2 5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 140 (accept_3_2 7 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 140
  2 3 10 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 20 140 5
  1 4 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 20 140 4 1
  5 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 20 140
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 20 140 2 1 10 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 20 140 (accept_3_2 1 20 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 20
  140)))))))))))))))))))) (allB_succ 19 140 (allA_of_3_0 19 19 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ
  18 140 (allA_succ_of_accept 17 18 140 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 18 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 140 2 8 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 140 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  15 18 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 18 140 2 7 9 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 140 (accept_3_2 13
  18 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 140 2 6 9 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 140
  (Polychromatic418967fa.accept_19_11_18_7_1_4466 11 18 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 140 2 5 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 18 140 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 18 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 140 2 4 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 140 (accept_3_2 7 18 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 18 140 2 3 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 18 140 (Polychromatic418967fa.accept_17_5_1_4_1_3460 5 18 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 140 2 2 9 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 140 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  18 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 18 140 2 1 9 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 140 (accept_3_2 1 18
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18 140)))))))))))))))))) (allB_succ 17 140 (allA_succ_of_accept
  16 17 140 (accept_3_2 16 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 17 140 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 17 140 (accept_3_2 13 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 17 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 17 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 11
  17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 140 (accept_3_2 10 17
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 140 (Polychromatic418967fa.accept_6_3_5_2_1_12
  9 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 140
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 140 (accept_3_2 7 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  140 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 140 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 140 (accept_3_2 4 17 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 140 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  17 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 140 (accept_3_2 1 17 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 140))))))))))))))))) (allB_succ 16 140 (allA_of_3_0 16 16 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 140 (allA_succ_of_accept 14 15 140
  (Polychromatic418967fa.accept_19_14_15_7_1_7205 14 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 140 (accept_3_2 13 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 140 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 15 140 5 2 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 15 140 (Polychromatic418967fa.accept_21_9_15_14_1_2790
  9 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 140
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 140 (accept_3_2 7 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  140 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 140 5 1 3 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 140 (accept_3_2 4 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15
  140 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 15 140 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 15 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 140 (accept_3_2 1 15 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 15 140))))))))))))))) (allB_succ 14 140 (allA_succ_of_accept 13 14 140 (accept_3_2 13 14 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 140 2 6 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 140 (Polychromatic418967fa.accept_12_11_2_8_1_511
  11 14 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 14 140 2 5 7 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 14 140
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 14 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 14 140 2 4 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 14 140 7 1 2 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 14 140 2 3 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 14 140 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 14 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 140 2 2 7 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 140 (Polychromatic418967fa.accept_19_3_14_7_1_7204 3 14 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 140 2 1 7 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 140 (accept_3_2 1 14 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 140)))))))))))))) (allB_succ 13 140 (allA_of_3_0 13 13 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 140 (allA_succ_of_accept 11 12 140
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 12 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 140 2 5 6 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 140 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 12 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 140 4 2 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 140 (accept_3_2 7 12 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 140 2 3 6 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 140 (Polychromatic418967fa.accept_19_5_12_7_1_4416 5 12 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 140 4 1 3 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 140 (Polychromatic418967fa.accept_18_3_12_14_1_2232
  3 12 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 140 2 1 6 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 140 (accept_3_2 1 12
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 140)))))))))))) (allB_succ 11 140 (allA_succ_of_accept 10 11
  140 (accept_3_2 10 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 140
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 140 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 11 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 140 (accept_3_2 7 11 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 140 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 11 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 140 (Polychromatic418967fa.accept_18_5_11_14_1_7203
  5 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 140 (accept_3_2 4 11
  140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 140 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 140
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 140 (accept_3_2 1 11 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  140))))))))))) (allB_succ 10 140 (allA_of_3_0 10 10 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 140
  (allA_succ_of_accept 8 9 140 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 9 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 140 (accept_3_2 7 9 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 140 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 9 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 140 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 140 (accept_3_2 4 9 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 140 (Polychromatic418967fa.accept_15_3_9_5_1_2082 3
  9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 140
  (Polychromatic418967fa.accept_16_2_9_12_1_46 2 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 140 (accept_3_2 1 9 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 140)))))))))
  (allB_succ 8 140 (allA_succ_of_accept 7 8 140 (accept_3_2 7 8 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 140 2 3 4 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 140 (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 8 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 140 4 1 2 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 140 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 8 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 140 2 1 4 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 140 (accept_3_2 1 8 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 140)))))))) (allB_succ 7 140 (allA_of_3_0 7 7 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 140 (allA_succ_of_accept 5 6 140 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 6
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 140 2 2 3 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 140
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 6 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 140 2 1 3 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 140 (accept_3_2 1 6 140 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 140))))))
  (allB_succ 5 140 (allA_succ_of_accept 4 5 140 (accept_3_2 4 5 140 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 140 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 140 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 5 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 140 (accept_3_2 1 5 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 140))))) (allB_succ 4 140 (allA_of_3_0 4 4 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 140 (allA_succ_of_accept 2 3 140 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 3 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 140 (accept_3_2 1 3 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 140))) (allB_succ 2 140 (allA_succ_of_accept 1 2 140 (accept_3_2 1 2 140
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 140)) (allB_two
  140))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


