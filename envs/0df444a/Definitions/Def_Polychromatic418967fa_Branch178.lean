-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch178
-- name    : Polychromatic418967fa_Branch178
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:52.42926+00:00
-- url     : https://prove2.me/theorems/1857ef99-8a3f-4f24-bb07-0fd422d42407
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

def Polychromatic418967fa.branch_178 : allB 178 178 :=
  allB_succ' 2 177 178 (Eq.refl Bool.true) (allA_succ_of_accept 1 177 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  177 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 178)) (allB_succ' 3 176 178
  (Eq.refl Bool.true) (allA_of_3_1 3 176 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 175 178 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 175 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 178 (accept_3_3 2 175 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 178)))) (allB_succ' 5 174 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 174 178 2 2 87 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 174 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 174 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 178 2 1 87 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 174 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 178))))) (allB_succ' 6 173 178 (Eq.refl
  Bool.true) (allA_of_3_1 6 173 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 172 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 172 178 2 3 86 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 178 (accept_3_3 5 172 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  178 2 2 86 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 172 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 178 2 1 86 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 172 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 178))))))) (allB_succ' 8 171 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 171 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 171 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 178 (accept_3_3 5 171 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 178 (Polychromatic418967fa.accept_11_4_6_2_1_51 4
  171 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 178
  (Polychromatic418967fa.accept_10_3_1_8_1_132 3 171 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 178 (accept_3_3 2 171 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 178)))))))) (allB_succ' 9 170 178 (Eq.refl Bool.true) (allA_of_3_1 9 170 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 169 178 (Eq.refl Bool.true) (allA_succ_of_accept 9 169 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 178 (accept_3_3 8 169 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 178 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 169 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 178 (accept_3_3 5 169 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 178 (accept_3_3 2 169 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 178 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 169 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 178)))))))))) (allB_succ' 11 168 178 (Eq.refl Bool.true) (allA_succ_of_gcd 10 168 178 2 5 84
  89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 178
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 168 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 178 2 4 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 178 (Polychromatic418967fa.accept_31_7_13_23_1_10049 7 168 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 178 2 3 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 178 (accept_3_3 5 168 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 178 2 2 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 168 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 178 2 1 84 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  168 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 178))))))))))) (allB_succ' 12 167
  178 (Eq.refl Bool.true) (allA_of_3_1 12 167 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 166 178
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 166 178 2 6 83 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 166 178 (accept_3_3 11 166 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 178 2 5 83 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 166 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 166 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 178 2 4 83 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 178 (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 166 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 178 2 3 83 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 178 (accept_3_3 5 166 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166 178 2 2 83 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 166 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  166 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 178 2 1 83 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 166 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 166 178))))))))))))) (allB_succ' 14 165 178 (Eq.refl Bool.true) (allA_succ_of_accept 13 165 178
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 165 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 165 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 178 (accept_3_3 11 165 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 165 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 165 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 178 (Polychromatic418967fa.accept_19_9_13_7_1_5830
  9 165 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 178 (accept_3_3 8
  165 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 165 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 165 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 178 (accept_3_3 5 165 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 165 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 165 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  165 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 178 (accept_3_3 2 165
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 178 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 165 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 178)))))))))))))) (allB_succ' 15
  164 178 (Eq.refl Bool.true) (allA_of_3_1 15 164 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 163 178
  (Eq.refl Bool.true) (allA_succ_of_accept 15 163 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 178 (accept_3_3 14 163 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 178 (accept_3_3 11 163 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 163 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 178 (accept_3_3 8 163 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 163 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 178 (accept_3_3 5 163 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 178 (accept_3_3 2 163 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 178)))))))))))))))) (allB_succ' 17 162 178 (Eq.refl
  Bool.true) (allA_succ_of_gcd 16 162 178 2 8 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 162 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 178 2 7 81 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 178
  (Polychromatic418967fa.accept_20_13_2_18_1_1682 13 162 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 178 2 6 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 178 (accept_3_3 11 162 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 178 2 5 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 162 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 162 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 178 2 4 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 178 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 162 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 178 2 3 81 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 178 (accept_3_3 5 162 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 178 2 2 81 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 162 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3
  162 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 178 2 1 81 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 178
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 162 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 178))))))))))))))))) (allB_succ' 18 161 178 (Eq.refl Bool.true) (allA_of_3_1 18 161 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 160 178 (Eq.refl Bool.true) (allA_succ_of_gcd 18 160 178 2 9 80 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 178
  (accept_3_3 17 160 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 178 2 8 80 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 178
  (Polychromatic418967fa.accept_11_4_6_2_1_51 15 160 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 160 178 2 7 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 160 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 160 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 178 2 6 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 178 (accept_3_3 11 160 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 178 2 5 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 178 2 4 80 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 160 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 178 2 3 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 178 (accept_3_3 5 160 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  178 2 2 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 178 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 160 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 178 2 1 80 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 160 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 160 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 178))))))))))))))))))) (allB_succ' 20 159 178 (Eq.refl
  Bool.true) (allA_succ_of_accept 19 159 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 178 (Polychromatic418967fa.accept_12_6_3_10_1_224
  18 159 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 178 (accept_3_3 17
  159 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 159 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 178 (accept_3_3 14 159 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 159 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 178 (Polychromatic418967fa.accept_9_3_6_7_1_562
  12 159 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 178 (accept_3_3 11
  159 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 10 159 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 159 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 178 (accept_3_3 8 159 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 159 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 178 (Polychromatic418967fa.accept_12_6_3_10_1_224
  6 159 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 178 (accept_3_3 5
  159 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 159 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 159 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 159 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 178 (accept_3_3 2 159 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 159 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 178)))))))))))))))))))) (allB_succ' 21 158 178 (Eq.refl
  Bool.true) (allA_of_3_1 21 158 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 157 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 157 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 178 (accept_3_3 20 157 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 157 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 178 (Polychromatic418967fa.accept_13_5_1_9_1_618
  18 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 178 (accept_3_3 17
  157 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 178
  (Polychromatic418967fa.accept_12_4_1_10_1_221 16 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 157 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 178 (accept_3_3 14 157 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 157 178 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 157 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 178 (accept_3_3 11 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 178 (accept_3_3 8 157 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 178 (accept_3_3 5 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 157 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 178 (accept_3_3 2 157 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 157 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 178)))))))))))))))))))))) (allB_succ' 23 156 178
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 156 178 2 11 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 178 (Polychromatic418967fa.accept_19_2_4_7_1_10048 21 156
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 178 2 10 78 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 178 2 9 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 178 (accept_3_3 17 156 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  156 178 2 8 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 156 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 156 178 2 7 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 156 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 178 2 6 78 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 178 (accept_3_3 11 156 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 178 2 5 78 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 178
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 156 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 178 2 4 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 178 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 156 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 178 2 3 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 178 (accept_3_3 5 156 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 178 2 2 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 156 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 178 2 1 78 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  156 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 178)))))))))))))))))))))))
  (allB_succ' 24 155 178 (Eq.refl Bool.true) (allA_of_3_1 24 155 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 154 178 (Eq.refl Bool.true) (allA_succ_of_gcd 24 154 178 2 12 77 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 154 178 (accept_3_3 23 154 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 178 2 11 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 154 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  154 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 178 2 10 77 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 154 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 178 2 9 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 154 178 (accept_3_3 17 154 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  154 178 2 8 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 154 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 154 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 178 2 7 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 178 2 6 77 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 178 (accept_3_3 11 154 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 178 2 5 77 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 154 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 178 2 4 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 178 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 154 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 178 2 3 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 178 (accept_3_3 5 154 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 178 2 2 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 154 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 178 2 1 77 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 178 (Polychromatic418967fa.accept_13_1_11_9_1_1857
  1 154 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 178)))))))))))))))))))))))))
  (allB_succ' 26 153 178 (Eq.refl Bool.true) (allA_succ_of_accept 25 153 178 (Polychromatic418967fa.accept_6_1_3_4_1_1
  25 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 178
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 178 (accept_3_3 23 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 178 (Polychromatic418967fa.accept_16_6_9_2_1_6518 22 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 153 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 178 (accept_3_3 20 153 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 178 (accept_3_3 17 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 178 (accept_3_3 14 153 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 178
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 178 (accept_3_3 11 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 178 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 178 (accept_3_3 8 153 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 178
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 178 (accept_3_3 5 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 178 (accept_3_3 2 153 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 178)))))))))))))))))))))))))) (allB_succ' 27 152 178
  (Eq.refl Bool.true) (allA_of_3_1 27 152 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 151 178 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 151 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 178 (accept_3_3 26 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 178
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 178 (accept_3_3 23 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 178 (accept_3_3 20 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 178 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 151 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 178
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 178 (accept_3_3 17 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 178 (accept_3_3 14 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 178
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 178 (accept_3_3 11 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 178 (accept_3_3 8 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 178 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 151 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 178 (accept_3_3 5 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 151 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 178 (accept_3_3 2 151 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 178)))))))))))))))))))))))))))) (allB_succ' 29 150
  178 (Eq.refl Bool.true) (allA_succ_of_gcd 28 150 178 2 14 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 150
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 178 2 13 75 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 178
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 150 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 178 2 12 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 178 (accept_3_3 23 150 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 178 2 11 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 178 2 10 75 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 150 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 178 2 9 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 178 (accept_3_3 17 150 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  150 178 2 8 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 150 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 150 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 150 178 2 7 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 150 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 150 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 178 2 6 75 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 178 (accept_3_3 11 150 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 178 2 5 75 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 178
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 150 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 178 2 4 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 178 (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 150 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 178 2 3 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 178 (accept_3_3 5 150 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 178 2 2 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 150 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 178 2 1 75 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  150 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 178)))))))))))))))))))))))))))))
  (allB_succ' 30 149 178 (Eq.refl Bool.true) (allA_of_3_1 30 149 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 148 178 (Eq.refl Bool.true) (allA_succ_of_gcd 30 148 178 2 15 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 178 (accept_3_3 29 148 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 178 2 14 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 178 (Polychromatic418967fa.accept_13_1_5_9_1_226
  27 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 178 2 13 74 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 178 2 12 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 178 (accept_3_3 23 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 178 2 11 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 148 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 178 2 10 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 178 2 9 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 178 (accept_3_3 17 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 178 2 8 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 178 2 7 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 148 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 178 2 6 74 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 178 (accept_3_3 11 148 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 178 2 5 74 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 178 2 4 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 148 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 178 2 3 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 178 (accept_3_3 5 148 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 178 2 2 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 148 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 178 2 1 74 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 178)))))))))))))))))))))))))))))))
  (allB_succ' 32 147 178 (Eq.refl Bool.true) (allA_succ_of_accept 31 147 178 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 178 (accept_3_3 29 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 178 (Polychromatic418967fa.accept_19_8_14_7_1_10047 27 147 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 178 (accept_3_3 26 147 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 178 (accept_3_3 23 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 178 (accept_3_3 20 147 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 178 (accept_3_3 17 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 178 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 178 (accept_3_3 14 147 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 178
  (Polychromatic418967fa.accept_19_12_14_7_1_5865 12 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 178 (accept_3_3 11 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 147 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 178 (accept_3_3 8 147 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 178 (accept_3_3 5 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 147 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 178 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 147 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 178 (accept_3_3 2 147 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 178))))))))))))))))))))))))))))))))
  (allB_succ' 33 146 178 (Eq.refl Bool.true) (allA_of_3_1 33 146 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 34 145 178 (Eq.refl Bool.true) (allA_succ_of_accept 33 145 178 (Polychromatic418967fa.accept_6_3_1_4_1_25
  33 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 178 (accept_3_3 32
  145 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 145 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 145 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 178 (accept_3_3 29 145 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 145 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 145 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 178 (accept_3_3 26 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 178 (Polychromatic418967fa.accept_16_9_1_2_1_2126 25 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 178 (accept_3_3 23 145 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 145 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 178 (accept_3_3 20 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 178 (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 145 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 178 (accept_3_3 17 145 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 178 (accept_3_3 14 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 178 (accept_3_3 11 145 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 145 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 178 (accept_3_3 8 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 145 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 178 (accept_3_3 5 145 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 145 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 178 (accept_3_3 2 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 178)))))))))))))))))))))))))))))))))) (allB_succ' 35 144 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 144 178 2 17 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 144 178 (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 144 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 178 2 16 72 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 178
  (Polychromatic418967fa.accept_13_5_1_9_1_618 31 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 178 2 15 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 178 (accept_3_3 29 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 178 2 14 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 144 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 178 2 13 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 178
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 178 2 12 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 178 (accept_3_3 23 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 178 2 11 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 178 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 144 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 178 2 10 72 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 178 2 9 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 178 (accept_3_3 17 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  144 178 2 8 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 144 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 178 2 7 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 178 2 6 72 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 178 (accept_3_3 11 144 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 178 2 5 72 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 144 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 178 2 4 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 178 (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 144 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 178 2 3 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 178 (accept_3_3 5 144 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 178 2 2 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 178 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 144 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 178 2 1 72 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  144 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  178))))))))))))))))))))))))))))))))))) (allB_succ' 36 143 178 (Eq.refl Bool.true) (allA_of_3_1 36 143 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 142 178 (Eq.refl Bool.true) (allA_succ_of_gcd 36 142 178 2 18 71 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 142 178
  (accept_3_3 35 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 142 178 2 17 71 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 142 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 142 178 2 16 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 142 178 (Polychromatic418967fa.accept_17_14_6_8_1_7688 31 142 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 142 178 2 15 71 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 142 178 (accept_3_3 29 142 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 142 178 2 14 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 142 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 142 178 2 13 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 142 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 142 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 142 178 2 12 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 142 178 (accept_3_3 23 142 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 142 178 2 11 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 142 178 (Polychromatic418967fa.accept_13_8_12_9_1_1168
  21 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 178 2 10 71 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 178 2 9 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 178 (accept_3_3 17 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 178 2 8 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 178 2 7 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 142 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 178 2 6 71 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 178 (accept_3_3 11 142 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 178 2 5 71 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 178
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 178 2 4 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 178 (Polychromatic418967fa.accept_20_7_2_18_1_5618 7 142 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 178 2 3 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 178 (accept_3_3 5 142 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 178 2 2 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 178 (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 142 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 178 2 1 71 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  142 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  178))))))))))))))))))))))))))))))))))))) (allB_succ' 38 141 178 (Eq.refl Bool.true) (allA_succ_of_accept 37 141 178
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 141 178 (Polychromatic418967fa.accept_20_16_1_18_1_5617 36 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 178 (accept_3_3 35 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 178 (Polychromatic418967fa.accept_13_8_11_9_1_593 34 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 178 (accept_3_3 32 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 178 (accept_3_3 29 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 178 (accept_3_3 26 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 178 (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 178 (accept_3_3 23 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 141 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 178 (accept_3_3 20 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 178 (accept_3_3 17 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 178 (accept_3_3 14 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 178 (accept_3_3 11 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 178 (accept_3_3 8 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 178 (accept_3_3 5 141 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 141 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 178 (accept_3_3 2 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 178)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 140 178 (Eq.refl Bool.true)
  (allA_of_3_1 39 140 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 139 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 139 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 178 (accept_3_3 38 139 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 178 (Polychromatic418967fa.accept_15_6_4_13_1_403
  36 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 178 (accept_3_3 35
  139 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 178
  (Polychromatic418967fa.accept_10_4_9_8_1_125 34 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 178 (accept_3_3 32 139 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 139 178 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 139 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 178 (accept_3_3 29 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 178 (accept_3_3 26 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 178 (accept_3_3 23 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 178 (Polychromatic418967fa.accept_16_6_11_2_1_6485 22 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 178 (accept_3_3 20 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 178 (accept_3_3 17 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 178 (accept_3_3 14 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 178 (accept_3_3 11 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 178 (accept_3_3 8 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 178 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 139 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 178 (accept_3_3 5 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 178 (accept_3_3 2 139 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139 178))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 138 178 (Eq.refl Bool.true) (allA_succ_of_gcd 40 138 178 2 20 69 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 178 2 19 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 138 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 138 178 2 18 69 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 138 178 (accept_3_3 35 138 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 178 2 17 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 33
  138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 178 2 16 69 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 178 2 15 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 178 (accept_3_3 29 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 178 2 14 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 138 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 178 2 13 69 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 178
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 178 2 12 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 178 (accept_3_3 23 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 178 2 11 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 138 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 178 2 10 69 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 178 2 9 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 178 (accept_3_3 17 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  138 178 2 8 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 138 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 138 178 2 7 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 138 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 138 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 178 2 6 69 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 178 (accept_3_3 11 138 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 178 2 5 69 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 178 2 4 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 178 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 138 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 178 2 3 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 178 (accept_3_3 5 138 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 178 2 2 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 138 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 178 2 1 69 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  138 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  178))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 137 178 (Eq.refl Bool.true) (allA_of_3_1 42 137 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 136 178 (Eq.refl Bool.true) (allA_succ_of_gcd 42 136 178 2 21
  68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 136 178
  (accept_3_3 41 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 136 178 2 20 68 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 136 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 136 178 2 19 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 136 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 136 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 178 2 18 68 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 178 (accept_3_3 35 136 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 178 2 17 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 178 2 16 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 136 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 178 2 15 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 178 (accept_3_3 29 136 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 178 2 14 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 178 (Polychromatic418967fa.accept_13_1_6_9_1_1197
  27 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 178 2 13 68 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 178 2 12 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 178 (accept_3_3 23 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 178 2 11 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 136 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 178 2 10 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 178 2 9 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 136 178 (accept_3_3 17 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  136 178 2 8 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 136 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 178 2 7 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 178 2 6 68 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 178 (accept_3_3 11 136 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 178 2 5 68 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 178
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 178 2 4 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 136 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 178 2 3 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 178 (accept_3_3 5 136 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 178 2 2 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 178 2 1 68 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  136 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  178))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 135 178 (Eq.refl Bool.true) (allA_succ_of_accept 43 135
  178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 135 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 135 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 178 (accept_3_3 41 135 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 135 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 135 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 178 (Polychromatic418967fa.accept_19_1_2_7_1_2054
  39 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 178 (accept_3_3 38
  135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 135 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 178 (accept_3_3 35 135 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 135 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 135 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 178 (accept_3_3 32
  135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 178
  (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 135 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 135 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 178 (accept_3_3 29 135 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 135 178 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 135 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 178 (accept_3_3 26 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 178 (Polychromatic418967fa.accept_17_7_16_8_1_7613 24 135 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 178 (accept_3_3 23 135 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 135 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 178 (accept_3_3 20 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 135 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 178 (accept_3_3 17 135 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 178 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 135
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 178 (accept_3_3 14 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 178 (accept_3_3 11 135 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 178 (Polychromatic418967fa.accept_20_10_15_18_1_7100 10 135 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 178 (accept_3_3 8 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 178 (accept_3_3 5 135 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 178 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 135 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 178
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 178 (accept_3_3 2 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 178)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 134 178 (Eq.refl Bool.true)
  (allA_of_3_1 45 134 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 133 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 133 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 178 (accept_3_3 44 133 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 133 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 178
  (Polychromatic418967fa.accept_20_2_13_18_1_5615 42 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 133 178 (accept_3_3 41 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 133 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 133 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 178 (accept_3_3 38 133 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 178
  (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 133 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 133 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 178 (accept_3_3 35 133 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 133 178 (Polychromatic418967fa.accept_13_8_3_9_1_5269 34 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 178 (accept_3_3 32 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 178 (Polychromatic418967fa.accept_21_9_7_10_1_3907 30 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 178 (accept_3_3 29 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 133
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 178 (accept_3_3 26 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 178 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 178 (Polychromatic418967fa.accept_17_7_14_8_1_5069 24 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 178 (accept_3_3 23 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 178 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 133
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 178 (accept_3_3 20 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 178 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 178 (accept_3_3 17 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 133
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 178 (accept_3_3 14 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 178 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 178 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 178 (accept_3_3 11 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 178 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 133
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 178 (accept_3_3 8 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 133 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 178 (accept_3_3 5 133 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 133 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 178 (accept_3_3 2 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 133 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 178)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 132 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 132 178 2 23 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 132 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 178 2 22 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 178
  (Polychromatic418967fa.accept_31_12_8_23_1_10046 43 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 132 178 2 21 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 132 178 (accept_3_3 41 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 178 2 20 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 178 2 19 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 178 2 18 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 178 (accept_3_3 35 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 178 2 17 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 132 178 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 132 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 178 2 16 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 178 2 15 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 178 (accept_3_3 29 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 178 2 14 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 132 178 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 132 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 178 2 13 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 178 2 12 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 178 (accept_3_3 23 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 178 2 11 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 132 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 178 2 10 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 178 2 9 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 178 (accept_3_3 17 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  132 178 2 8 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 132 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 178 2 7 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 178 2 6 66 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 178 (accept_3_3 11 132 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 178 2 5 66 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 178 2 4 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 178 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 132 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 178 2 3 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 178 (accept_3_3 5 132 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 178 2 2 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 132 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 178 2 1 66 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  132 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  178))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 131 178 (Eq.refl Bool.true) (allA_of_3_1 48 131 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 130 178 (Eq.refl Bool.true) (allA_succ_of_gcd 48 130 178 2 24
  65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 130 178
  (accept_3_3 47 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 130 178 2 23 65 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 130 178
  (Polychromatic418967fa.accept_20_5_10_18_1_5622 45 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 130 178 2 22 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 130 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 130 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 130 178 2 21 65 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 130 178 (accept_3_3 41 130 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 178 2 20 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 130 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 130 178 2 19 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 130 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 130 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 178 2 18 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 130 178 (accept_3_3 35 130 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 130 178 2 17 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 33
  130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 178 2 16 65 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 178
  (Polychromatic418967fa.accept_15_1_10_13_1_939 31 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 178 2 15 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 178 (accept_3_3 29 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 178 2 14 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 130 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 178 2 13 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 178
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 25 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 178 2 12 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 178 (accept_3_3 23 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 178 2 11 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 130 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 178 2 10 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 178
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 178 2 9 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 178 (accept_3_3 17 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 178 2 8 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 178 2 7 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 130 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 178 2 6 65 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 178 (accept_3_3 11 130 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 178 2 5 65 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 178
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 178 2 4 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 130 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 178 2 3 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 178 (accept_3_3 5 130 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 178 2 2 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 130 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 178 2 1 65 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  130 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  178))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 129 178 (Eq.refl Bool.true) (allA_succ_of_accept
  49 129 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 178 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 178 (accept_3_3 47 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 129 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 178
  (Polychromatic418967fa.accept_24_21_9_10_1_10036 45 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 178 (accept_3_3 44 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 178 (accept_3_3 41 129 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 178 (Polychromatic418967fa.accept_9_4_3_7_1_296
  40 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 178 (accept_3_3 38 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 178 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 178 (accept_3_3 35 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 129
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 178 (accept_3_3 32 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 178 (accept_3_3 29 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 129 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 178 (accept_3_3 26 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 178 (accept_3_3 23 129 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 178
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 178 (accept_3_3 20 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 178 (accept_3_3 17 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 129
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 178 (accept_3_3 14 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 178 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 178 (accept_3_3 11 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 178
  (Polychromatic418967fa.accept_16_9_1_2_1_2126 9 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 178 (accept_3_3 8 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 129 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 178 (accept_3_3 5 129 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 129 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 178 (accept_3_3 2 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 178)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 128 178 (Eq.refl
  Bool.true) (allA_of_3_1 51 128 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 127 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 127 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 178 (accept_3_3 50 127 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 48
  127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 178 (accept_3_3 47
  127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 178 (accept_3_3 44 127 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 127 178 (Polychromatic418967fa.accept_18_7_1_16_1_578 43 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 178 (accept_3_3 41 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 178 (accept_3_3 38 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 178
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 178 (accept_3_3 35 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 178 (Polychromatic418967fa.accept_19_15_13_7_1_7246 34 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 178 (accept_3_3 32 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 178 (accept_3_3 29 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 178 (accept_3_3 26 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 178 (accept_3_3 23 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 178 (accept_3_3 20 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 178 (accept_3_3 17 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 178 (accept_3_3 14 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 178 (accept_3_3 11 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 178 (accept_3_3 8 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 178 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 178 (accept_3_3 5 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 178 (accept_3_3 2 127 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  178)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 126 178 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 126 178 2 26 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 126 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 126 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 178 2 25 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 178 (Polychromatic418967fa.accept_15_4_6_13_1_956
  49 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 126 178 2 24 63 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 178
  (accept_3_3 47 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 178 2 23 63 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 178 2 22 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 126 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 178 2 21 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 178 (accept_3_3 41 126 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 178 2 20 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 178 2 19 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 178 (Polychromatic418967fa.accept_15_7_6_13_1_936 37 126 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 178 2 18 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 126 178 (accept_3_3 35 126 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 178 2 17 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 178
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 178 2 16 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 178 (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 126 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 178 2 15 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 178 (accept_3_3 29 126 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 178 2 14 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 178 2 13 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 178 (Polychromatic418967fa.accept_22_3_16_2_1_10045 25 126 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 178 2 12 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 178 (accept_3_3 23 126 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 178 2 11 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 178 2 10 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 178 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 126 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 178 2 9 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 178 (accept_3_3 17 126 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 178 2 8 63 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 15 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 178 2 7 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 126 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 178 2 6 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 178 (accept_3_3 11 126 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 178 2 5 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 126 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 178 2 4 63 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 178
  (Polychromatic418967fa.accept_15_7_6_13_1_936 7 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 178 2 3 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 178 (accept_3_3 5 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  178 2 2 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 126 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 178 2 1 63 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 126 178 (Polychromatic418967fa.accept_17_1_7_8_1_6347 1 126 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 178)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 125 178 (Eq.refl Bool.true) (allA_of_3_1 54 125 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 55 124 178 (Eq.refl Bool.true) (allA_succ_of_gcd 54 124 178 2 27 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 124 178 (accept_3_3 53 124 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 124 178 2 26 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 124 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 51
  124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 178 2 25 62 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 178 2 24 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 178 (accept_3_3 47 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 178 2 23 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 178 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 124 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 178 2 22 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 178 2 21 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 178 (accept_3_3 41 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 178 2 20 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 124 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 178 2 19 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 178 2 18 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 178 (accept_3_3 35 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 178 2 17 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 178 (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 124 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 178 2 16 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 178 2 15 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 178 (accept_3_3 29 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 178 2 14 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 178 (Polychromatic418967fa.accept_25_2_24_3_1_4507 27 124 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 178 2 13 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 178 2 12 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 178 (accept_3_3 23 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 178 2 11 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 178 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 124 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 178 2 10 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 178 2 9 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 178 (accept_3_3 17 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 178 2 8 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 178 2 7 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 124 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 178 2 6 62 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 178 (accept_3_3 11 124 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 178 2 5 62 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 178 2 4 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 124 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 178 2 3 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 178 (accept_3_3 5 124 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 178 2 2 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 178 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 124 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 178 2 1 62 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  124 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 123 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 123 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 123
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 178 (accept_3_3 53 123
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 178
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 52 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 123 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 178 (accept_3_3 50 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 178 (Polychromatic418967fa.accept_7_6_4_3_1_266
  48 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 178 (accept_3_3 47
  123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 178 (accept_3_3 44 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 123 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 178 (Polychromatic418967fa.accept_12_6_3_10_1_224
  42 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 178 (accept_3_3 41
  123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 123 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 178 (accept_3_3 38 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 36
  123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 178 (accept_3_3 35
  123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 178 (accept_3_3 32 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 123 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 178 (Polychromatic418967fa.accept_9_3_6_7_1_562
  30 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 178 (accept_3_3 29
  123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 123 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 178 (accept_3_3 26 123 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 178
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 123 178 (accept_3_3 23 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 123 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 178 (accept_3_3 20 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 123 178 (accept_3_3 17 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 123 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 123 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 178 (accept_3_3 14 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 123 178 (accept_3_3 11 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 123 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 178 (accept_3_3 8 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 123 178 (accept_3_3 5 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  123 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 123 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 123 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 178 (accept_3_3 2 123 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 122 178 (Eq.refl Bool.true) (allA_of_3_1 57
  122 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 121 178 (Eq.refl Bool.true) (allA_succ_of_accept 57
  121 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 121 178 (accept_3_3 56 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 121 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 121 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 121 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 178 (accept_3_3 53 121 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 178 (Polychromatic418967fa.accept_12_4_1_10_1_221
  52 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 178 (accept_3_3 50 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 178 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 178 (accept_3_3 47 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 178 (accept_3_3 44 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 178 (accept_3_3 41 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 178 (accept_3_3 38 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 178 (accept_3_3 35 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 178 (accept_3_3 32 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 178 (accept_3_3 29 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 178 (accept_3_3 26 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 178 (accept_3_3 23 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 178 (accept_3_3 20 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 178 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 178 (accept_3_3 17 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 121
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 178 (accept_3_3 14 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 178 (accept_3_3 11 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 178 (accept_3_3 8 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 178 (accept_3_3 5 121 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 121 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 178 (accept_3_3 2 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 120 178
  (Eq.refl Bool.true) (allA_succ_of_gcd 58 120 178 2 29 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 120 178 (Polychromatic418967fa.accept_13_5_3_9_1_1189 57 120
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 120 178 2 28 60 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 178 2 27 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 120 178 (accept_3_3 53 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 120 178 2 26 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 120 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 120 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 120 178 2 25 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 178 2 24 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 178 (accept_3_3 47 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 178 2 23 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 120 178 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 120 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 120 178 2 22 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 178
  (Polychromatic418967fa.accept_17_9_1_8_1_5045 43 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 178 2 21 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 178 (accept_3_3 41 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 178 2 20 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 120 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 120 178 2 19 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 178 2 18 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 178 (accept_3_3 35 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 178 2 17 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 120 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 120 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 178 2 16 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 178 2 15 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 178 (accept_3_3 29 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 178 2 14 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 120 178 (Polychromatic418967fa.accept_18_9_12_16_1_7323 27 120 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 178 2 13 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 178 2 12 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 178 (accept_3_3 23 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 178 2 11 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 120 178 (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 120 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 178 2 10 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 178 2 9 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 178 (accept_3_3 17 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  120 178 2 8 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 120 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 120 178 2 7 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 120 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 120 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 178 2 6 60 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 178 (accept_3_3 11 120 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 178 2 5 60 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 120 178 2 4 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 178 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 120 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 178 2 3 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 178 (accept_3_3 5 120 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 120 178 2 2 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 120 178 (Polychromatic418967fa.accept_19_3_6_7_1_10044 3 120 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 178 2 1 60 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 120
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 119 178 (Eq.refl Bool.true) (allA_of_3_1
  60 119 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 118 178 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  118 178 2 30 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 118 178 (accept_3_3 59 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  118 178 2 29 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 118 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 118 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 178 2 28 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 178 (Polychromatic418967fa.accept_18_1_10_16_1_566
  55 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 118 178 2 27 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 118 178
  (accept_3_3 53 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 118 178 2 26 59 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 118 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 118 178 2 25 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 118 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 118 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 118 178 2 24 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 118 178 (accept_3_3 47 118 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 118 178 2 23 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 118 178 (Polychromatic418967fa.accept_13_6_1_9_1_619
  45 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 178 2 22 59 89
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 178
  (Polychromatic418967fa.accept_16_11_6_2_1_4155 43 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 178 2 21 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 178 (accept_3_3 41 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 178 2 20 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 118 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 178 2 19 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 178 2 18 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 178 (accept_3_3 35 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 178 2 17 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 118 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 178 2 16 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 178
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 178 2 15 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 178 (accept_3_3 29 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 178 2 14 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 118 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 178 2 13 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 178 2 12 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 178 (accept_3_3 23 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 178 2 11 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 118 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 178 2 10 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 178
  (Polychromatic418967fa.accept_13_6_1_9_1_619 19 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 178 2 9 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 178 (accept_3_3 17 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 178 2 8 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 178 2 7 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 118 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 178 2 6 59 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 178 (accept_3_3 11 118 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 178 2 5 59 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 178 2 4 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 178 (Polychromatic418967fa.accept_17_7_16_8_1_7613 7 118 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 178 2 3 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 178 (accept_3_3 5 118 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 178 2 2 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 118 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 178 2 1 59 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 178 (Polychromatic418967fa.accept_16_1_6_2_1_3100 1
  118 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 117 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 117 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 117 178 (Polychromatic418967fa.accept_25_10_17_3_1_10043 60
  117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 117 178 (accept_3_3 59
  117 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 117 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 117 178 (accept_3_3 56 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 117 178 (Polychromatic418967fa.accept_12_6_9_10_1_565
  54 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 117 178 (accept_3_3 53
  117 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 178
  (Polychromatic418967fa.accept_19_14_3_7_1_7248 52 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 117 178 (accept_3_3 50 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 117 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 117 178
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 117 178 (accept_3_3 47 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 178 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 117 178 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 117
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 117 178 (accept_3_3 44 117
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 117 178 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 178 (accept_3_3 41 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 117 178 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 117 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 117 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 117 178 (accept_3_3 38 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 117 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 117 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 178 (accept_3_3 35 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 178 (Polychromatic418967fa.accept_19_15_3_7_1_5875 34 117 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 117 178
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 33 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 178 (accept_3_3 32 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 178 (accept_3_3 29 117 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 178
  (Polychromatic418967fa.accept_27_1_9_16_1_10028 28 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 178 (accept_3_3 26 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 178
  (Polychromatic418967fa.accept_19_5_3_7_1_10042 24 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 178 (accept_3_3 23 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 178 (Polychromatic418967fa.accept_20_1_17_18_1_1678 21 117 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 178 (accept_3_3 20 117 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 178 (accept_3_3 17 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 178 (accept_3_3 14 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 178
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 117 178 (accept_3_3 11 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 178 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 9
  117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 178 (accept_3_3 8 117
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 178 (accept_3_3 5 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 178 (Polychromatic418967fa.accept_19_4_3_7_1_5876 4 117 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 178 (accept_3_3 2 117 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 116 178 (Eq.refl Bool.true)
  (allA_of_3_1 63 116 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 115 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 115 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 178 (accept_3_3 62 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 178 (Polychromatic418967fa.accept_13_8_11_9_1_593
  60 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 178 (accept_3_3 59
  115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 178
  (Polychromatic418967fa.accept_18_4_7_16_1_2307 58 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 178 (accept_3_3 56 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 115 178 (Polychromatic418967fa.accept_14_13_3_10_1_2159 55 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 178
  (Polychromatic418967fa.accept_13_2_11_9_1_591 54 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 178 (accept_3_3 53 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 178 (accept_3_3 50 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 178
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 178 (accept_3_3 47 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 178 (Polychromatic418967fa.accept_13_7_11_9_1_1858 46 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 178 (accept_3_3 44 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 178
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 178 (accept_3_3 41 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 178 (accept_3_3 38 115 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 178
  (Polychromatic418967fa.accept_20_16_15_18_1_5605 36 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 115 178 (accept_3_3 35 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 115 178 (Polychromatic418967fa.accept_13_8_11_9_1_593 34 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 178 (accept_3_3 32 115 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 178
  (Polychromatic418967fa.accept_15_1_10_13_1_939 31 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 115 178 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 178 (accept_3_3 29 115 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 115 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 178 (accept_3_3 26 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 178 (Polychromatic418967fa.accept_25_24_15_3_1_10041 24 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 178 (accept_3_3 23 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 115
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 178 (accept_3_3 20 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 178 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 178 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 178 (accept_3_3 17 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 115
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 178 (accept_3_3 14 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 178 (accept_3_3 11 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 178 (Polychromatic418967fa.accept_19_10_1_7_1_10040 10 115
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 178 (accept_3_3 8 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 178 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 178 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 178 (accept_3_3 5 115 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 115 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 178 (accept_3_3 2 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 114 178
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 114 178 2 32 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 114 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 114
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 114 178 2 31 57 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 178 2 30 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 178 (accept_3_3 59 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 178 2 29 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 114 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 114 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 114 178 2 28 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 178 2 27 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 178 (accept_3_3 53 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 178 2 26 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 114 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 114 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 114 178 2 25 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 178 2 24 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 178 (accept_3_3 47 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 178 2 23 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 114 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 178 2 22 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 178 2 21 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 178 (accept_3_3 41 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 178 2 20 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 114 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 114 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 114 178 2 19 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 178 2 18 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 178 (accept_3_3 35 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 178 2 17 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 114 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 178 2 16 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 178 2 15 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 178 (accept_3_3 29 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 178 2 14 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 114 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 178 2 13 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 178
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 114 178 2 12 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 114 178 (accept_3_3 23 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 178 2 11 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 114 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 178 2 10 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 178 2 9 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 178 (accept_3_3 17 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 178 2 8 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 178 2 7 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 114 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 178 2 6 57 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 178 (accept_3_3 11 114 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 178 2 5 57 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 178 2 4 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 178 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 114 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 178 2 3 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 178 (accept_3_3 5 114 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 178 2 2 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 114 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 178 2 1 57 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  114 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 113 178 (Eq.refl Bool.true)
  (allA_of_3_1 66 113 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 112 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 112 178 2 33 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 112 178 (accept_3_3 65 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 178 2 32 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 178 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 112 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 178 2 31 56 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 178 2 30 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 178 (accept_3_3 59 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 178 2 29 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 178 2 28 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 178
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 178 2 27 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 178 (accept_3_3 53 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 178 2 26 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 178 2 25 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 178 2 24 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 178 (accept_3_3 47 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 178 2 23 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 178 2 22 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 178 2 21 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 178 (accept_3_3 41 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 178 2 20 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 178 2 19 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 178
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 178 2 18 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 178 (accept_3_3 35 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 178 2 17 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 178 2 16 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 178 2 15 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 178 (accept_3_3 29 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 178 2 14 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 178 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 112 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 178 2 13 56 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 178 2 12 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 178 (accept_3_3 23 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 178 2 11 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 178 2 10 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 178
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 178 2 9 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 178 (accept_3_3 17 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 178 2 8 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 178 2 7 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 112 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 178 2 6 56 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 178 (accept_3_3 11 112 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 178 2 5 56 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 178
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 112 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 178 2 4 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 112 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 178 2 3 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 178 (accept_3_3 5 112 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 178 2 2 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 112 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 178 2 1 56 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 112
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 111 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 111 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 111 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 111 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 66 111
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 111 178 (accept_3_3 65 111
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 178 (Polychromatic418967fa.accept_9_1_3_7_1_6
  64 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 111 178
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 111 178 (accept_3_3 62 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 111 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 111 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 111 178 (accept_3_3 59 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 111 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 111 178 (accept_3_3 56 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 111 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 111 178 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 111 178 (accept_3_3 53 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 178 (Polychromatic418967fa.accept_15_7_6_13_1_936 52 111
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 178 (accept_3_3 50 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 111 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 178 (Polychromatic418967fa.accept_19_10_16_7_1_10039 48 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 178 (accept_3_3 47 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 111 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 111 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 111 178 (accept_3_3 44 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 111 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 111 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 178 (accept_3_3 41 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 111 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 111 178 (accept_3_3 38 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 111 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 111 178 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 178 (accept_3_3 35 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 178 (Polychromatic418967fa.accept_13_8_7_9_1_611 34 111
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 178 (accept_3_3 32 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 178 (accept_3_3 29 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 178
  (Polychromatic418967fa.accept_19_8_16_7_1_8716 27 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 111 178 (accept_3_3 26 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 111 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 111 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 178 (accept_3_3 23 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 178 (accept_3_3 20 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 178 (accept_3_3 17 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 178 (accept_3_3 14 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 178 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 178 (accept_3_3 11 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 111 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 178 (accept_3_3 8 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 178 (accept_3_3 5 111 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 178
  (Polychromatic418967fa.accept_10_3_1_8_1_132 3 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 178 (accept_3_3 2 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 110
  178 (Eq.refl Bool.true) (allA_of_3_1 69 110 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 109 178
  (Eq.refl Bool.true) (allA_succ_of_accept 69 109 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 178 (accept_3_3 68 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 178 (accept_3_3 65 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 178 (accept_3_3 62 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 178 (Polychromatic418967fa.accept_10_1_9_8_1_123 61 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 178 (accept_3_3 59 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 178 (accept_3_3 56 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 178
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 178 (accept_3_3 53 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 178 (accept_3_3 50 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 178 (accept_3_3 47 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 46 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 178 (accept_3_3 44 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 178 (accept_3_3 41 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 178 (accept_3_3 38 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 178 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 178 (accept_3_3 35 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 178 (accept_3_3 32 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 178 (accept_3_3 29 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 178 (accept_3_3 26 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 178 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 109 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 178 (accept_3_3 23 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 178 (accept_3_3 20 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 178
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 178 (accept_3_3 17 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 178 (accept_3_3 14 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 178 (accept_3_3 11 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 178 (Polychromatic418967fa.accept_15_10_4_13_1_4506 10 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 178 (accept_3_3 8 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 178 (accept_3_3 5 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 109 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 178 (accept_3_3 2 109 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 108 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 108 178 2 35 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 108 178 (Polychromatic418967fa.accept_15_9_3_13_1_1686 69 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 108 178 2 34 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 178
  (Polychromatic418967fa.accept_25_17_8_3_1_10038 67 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 108 178 2 33 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 108 178 (accept_3_3 65 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 108 178 2 32 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 108 178 (Polychromatic418967fa.accept_16_15_12_2_1_6502 63 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 108 178 2 31 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 178
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 61 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 178 2 30 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 178 (accept_3_3 59 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 108 178 2 29 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 108 178 (Polychromatic418967fa.accept_13_5_4_9_1_601 57 108 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 108 178 2 28 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 178
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 55 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 108 178 2 27 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 108 178 (accept_3_3 53 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 178 2 26 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 108 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 178 2 25 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 178
  (Polychromatic418967fa.accept_16_1_12_2_1_2136 49 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 178 2 24 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 178 (accept_3_3 47 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 178 2 23 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 178 (Polychromatic418967fa.accept_13_6_4_9_1_4326 45 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 178 2 22 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 178
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 43 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 178 2 21 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 178 (accept_3_3 41 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 178 2 20 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 178 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 178 2 19 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 178
  (Polychromatic418967fa.accept_11_4_9_2_1_259 37 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 178 2 18 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 178 (accept_3_3 35 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 108 178 2 17 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 108 178 (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 178 2 16 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 178
  (Polychromatic418967fa.accept_13_5_4_9_1_601 31 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 178 2 15 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 178 (accept_3_3 29 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 108 178 2 14 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 108 178 (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 108 178 2 13 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 178
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 25 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 108 178 2 12 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 108 178 (accept_3_3 23 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 108 178 2 11 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 108 178 (Polychromatic418967fa.accept_13_8_4_9_1_1145 21 108 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 178 2 10 54 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 178
  (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 178 2 9 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 178 (accept_3_3 17 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  108 178 2 8 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 108 178 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 178 2 7 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 178 (Polychromatic418967fa.accept_20_13_8_18_1_8672 13 108 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 178 2 6 54 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 178 (accept_3_3 11
  108 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 178 2 5 54 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 178
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 178 2 4 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 108 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 178 2 3 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 178 (accept_3_3 5 108 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 178 2 2 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 178 (Polychromatic418967fa.accept_19_3_13_7_1_7245 3 108 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 178 2 1 54 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 178 (Polychromatic418967fa.accept_15_1_3_13_1_2548
  1 108 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 107 178 (Eq.refl Bool.true)
  (allA_of_3_1 72 107 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 106 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 106 178 2 36 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 178 (accept_3_3 71 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 178 2 35 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 178 (Polychromatic418967fa.accept_17_1_4_8_1_5049 69 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 178 2 34 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 178 2 33 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 178 (accept_3_3 65 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 178 2 32 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 178 2 31 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 178 2 30 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 178 (accept_3_3 59 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 178 2 29 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 178 (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 178 2 28 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 178
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 55 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 178 2 27 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 178 (accept_3_3 53 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 178 2 26 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 106 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 178 2 25 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 178
  (Polychromatic418967fa.accept_21_7_1_10_1_8571 49 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 178 2 24 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 178 (accept_3_3 47 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 178 2 23 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 178 (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 178 2 22 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 178
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 178 2 21 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 178 (accept_3_3 41 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 178 2 20 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 106 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 178 2 19 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 178 2 18 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 178 (accept_3_3 35 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 178 2 17 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 106 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 178 2 16 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 178
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 178 2 15 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 178 (accept_3_3 29 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 178 2 14 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 178 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 178 2 13 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 178 2 12 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 178 (accept_3_3 23 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 178 2 11 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 178 (Polychromatic418967fa.accept_25_21_6_3_1_10037 21 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 178 2 10 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 178 2 9 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 178 (accept_3_3 17 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 178 2 8 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 178 (Polychromatic418967fa.accept_19_15_11_7_1_8711 15 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 178 2 7 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 106 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 178 2 6 53 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 178 (accept_3_3 11 106 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 178 2 5 53 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 178 2 4 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 178 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 106 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 178 2 3 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 178 (accept_3_3 5 106 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 178 2 2 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 106 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 178 2 1 53 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 178 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1
  106 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 105 178 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 105 178 (Polychromatic418967fa.accept_10_2_5_8_1_139
  72 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 105 178 (accept_3_3 71
  105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 105 178
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 105 178 (Polychromatic418967fa.accept_24_21_9_10_1_10036 69 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 105 178 (accept_3_3 68 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 105 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 105 178 (accept_3_3 65 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 105 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 105 178 (accept_3_3 62 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 105 178
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 105 178 (accept_3_3 59 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 105 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 105 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 178 (accept_3_3 56 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 178 (accept_3_3 53 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 105 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 178 (accept_3_3 50 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 105 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 105 178 (accept_3_3 47 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 105 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 105 178 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 178 (accept_3_3 44 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 105 178
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 105 178 (accept_3_3 41 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 105 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 178 (accept_3_3 38 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 178
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 105 178 (accept_3_3 35 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 105 178 (Polychromatic418967fa.accept_13_8_1_9_1_1178 34 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 105 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 178 (accept_3_3 32 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 105 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 105 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 105 178 (accept_3_3 29 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 105 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 178 (accept_3_3 26 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 105 178
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 105 178 (accept_3_3 23 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 105 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 105 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 178 (accept_3_3 20 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 105 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 105 178 (accept_3_3 17 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 105 178 (Polychromatic418967fa.accept_19_16_10_7_1_8710 16 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 178 (accept_3_3 14 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 178 (accept_3_3 11 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 105 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 105 178 (Polychromatic418967fa.accept_18_9_15_16_1_8759 9 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 178 (accept_3_3 8 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 105 178 (accept_3_3 5 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  105 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 105 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 105 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 178 (accept_3_3 2 105 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 104 178 (Eq.refl
  Bool.true) (allA_of_3_1 75 104 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 103 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 103 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 178 (accept_3_3 74 103 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 72
  103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 178 (accept_3_3 71
  103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 178
  (Polychromatic418967fa.accept_21_7_19_10_1_8567 70 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 178 (accept_3_3 68 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 178 (Polychromatic418967fa.accept_21_4_19_10_1_8531 67 103 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 178 (accept_3_3 65 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 178 (accept_3_3 62 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 178 (accept_3_3 59 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 178 (accept_3_3 56 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 178
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 103 178 (accept_3_3 53 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 103 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 103 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 103 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 178 (accept_3_3 50 103 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 178 (accept_3_3 47 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 178 (accept_3_3 44 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 178 (accept_3_3 41 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 178 (accept_3_3 38 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 178 (accept_3_3 35 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 178 (Polychromatic418967fa.accept_13_8_12_9_1_1168 34 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 178 (accept_3_3 32 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 178 (accept_3_3 29 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 178 (accept_3_3 26 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 178 (accept_3_3 23 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 178 (accept_3_3 20 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 178
  (Polychromatic418967fa.accept_19_18_8_7_1_4446 18 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 178 (accept_3_3 17 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 178 (accept_3_3 14 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 178 (accept_3_3 11 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 178 (accept_3_3 8 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 178 (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 178 (accept_3_3 5 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 103 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 178 (accept_3_3 2 103 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 102 178 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 102 178 2 38 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 102 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 75 102 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 102 178 2 37 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 178 2 36 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 178 (accept_3_3 71 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 102 178 2 35 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 102 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 102 178 2 34 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 178 2 33 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 178 (accept_3_3 65 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 102 178 2 32 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 102 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 102 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 102 178 2 31 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 178
  (Polychromatic418967fa.accept_15_1_12_13_1_944 61 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 178 2 30 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 178 (accept_3_3 59 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 102 178 2 29 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 102 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 102 178 2 28 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 178 2 27 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 178 (accept_3_3 53 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 102 178 2 26 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 102 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 102 178 2 25 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 178 2 24 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 178 (accept_3_3 47 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 102 178 2 23 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 102 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 102 178 2 22 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 178 2 21 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 178 (accept_3_3 41 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 102 178 2 20 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 102 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 102 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 178 2 19 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 178 2 18 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 178 (accept_3_3 35 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 178 2 17 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 178 2 16 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 178 2 15 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 178 (accept_3_3 29 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 178 2 14 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 178 2 13 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 178 2 12 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 178 (accept_3_3 23 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 178 2 11 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 102 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 178 2 10 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 178 2 9 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 178 (accept_3_3 17 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 178 2 8 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 178 2 7 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 102 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 178 2 6 51 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 178 (accept_3_3 11 102 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 178 2 5 51 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 178 2 4 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 178 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 102 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 178 2 3 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 178 (accept_3_3 5 102 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 178 2 2 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 102 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 178 2 1 51 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  102 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 101 178 (Eq.refl
  Bool.true) (allA_of_3_1 78 101 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 100 178 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 100 178 2 39 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 100 178 (accept_3_3 77 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 100 178 2 38 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 100 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 100 178 2 37 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 100 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 100 178 2 36 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 100 178 (accept_3_3 71 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 100 178 2 35 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 100 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 100 178 2 34 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 100 178
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 100 178 2 33 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 100 178 (accept_3_3 65 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 100 178 2 32 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 100 178 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 100 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 100 178 2 31 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 100 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 178 2 30 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 178 (accept_3_3 59 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 100 178 2 29 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 100 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 100 178 2 28 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 100 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 100 178 2 27 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 100 178 (accept_3_3 53 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 100 178 2 26 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 100 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 178 2 25 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 178
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 100 178 2 24 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 100 178 (accept_3_3 47 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 100 178 2 23 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 100 178 (Polychromatic418967fa.accept_21_3_16_10_1_3911 45 100 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 100 178 2 22 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 100 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 100 178 2 21 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 100 178 (accept_3_3 41 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 100 178 2 20 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 100 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 178 2 19 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 100 178 2 18 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 100 178 (accept_3_3 35 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 178 2 17 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 178 2 16 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 178
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 178 2 15 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 178 (accept_3_3 29 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 178 2 14 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 100 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 178 2 13 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 178
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 25 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 178 2 12 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 100 178 (accept_3_3 23 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 100 178 2 11 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 100 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 178 2 10 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 100 178 2 9 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 100 178 (accept_3_3 17 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  100 178 2 8 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 100 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 100 178 2 7 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 100 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 100 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 178 2 6 50 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 178 (accept_3_3 11 100 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 178 2 5 50 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 178
  (Polychromatic418967fa.accept_19_9_5_7_1_5853 9 100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 100 178 2 4 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 100 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 100 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 178 2 3 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 178 (accept_3_3 5 100 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 100 178 2 2 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 100 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 100 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 178 2 1 50 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  100 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 99 178 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 99 178 (Polychromatic418967fa.accept_12_6_3_10_1_224
  78 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 99 178 (accept_3_3 77
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 99 178
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 76 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 99 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 99 178 (accept_3_3 74 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 99 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 72
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 99 178 (accept_3_3 71 99
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 99 178
  (Polychromatic418967fa.accept_16_6_3_2_1_3096 70 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 99 178 (accept_3_3 68 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 99 178 (Polychromatic418967fa.accept_12_6_3_10_1_224
  66 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 99 178 (accept_3_3 65
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 178
  (Polychromatic418967fa.accept_10_4_9_8_1_125 64 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 99 178 (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 178 (accept_3_3 62 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 99 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 60
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 99 178 (accept_3_3 59 99
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 58 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 178 (accept_3_3 56 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 99 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 54
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 99 178 (accept_3_3 53 99
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 178
  (Polychromatic418967fa.accept_15_7_9_13_1_3451 52 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 99 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 178 (accept_3_3 50 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 178 (Polychromatic418967fa.accept_15_3_9_13_1_1681
  48 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 178 (accept_3_3 47
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 46 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 178 (accept_3_3 44 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 178 (Polychromatic418967fa.accept_12_6_3_10_1_224
  42 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 178 (accept_3_3 41
  99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 99 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 178 (accept_3_3 38 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 178
  (Polychromatic418967fa.accept_22_14_11_2_1_8495 36 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 99 178 (accept_3_3 35 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  99 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 178 (accept_3_3 32 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 99 178 (accept_3_3 29 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  99 178 (Polychromatic418967fa.accept_17_11_14_8_1_2729 28 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 99 178 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 178 (accept_3_3 26 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 99 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 178
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 99 178 (accept_3_3 23 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  99 178 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 178 (accept_3_3 20 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 99 178 (accept_3_3 17 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  99 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 99 178 (Polychromatic418967fa.accept_16_15_3_2_1_4170 15 99 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 178 (accept_3_3 14 99 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 99 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 99 178 (accept_3_3 11 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  99 178 (Polychromatic418967fa.accept_23_10_7_17_1_10035 10 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 178 (accept_3_3 8 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 178 (accept_3_3 5 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99
  178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 99 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 99 178 (Polychromatic418967fa.accept_13_3_8_9_1_1134 3 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 178 (accept_3_3 2 99 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 99 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 99 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 98 178 (Eq.refl
  Bool.true) (allA_of_3_1 81 98 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 97 178 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 97 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 97 178 (accept_3_3 80 97 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 97 178
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 78 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 97 178 (accept_3_3 77 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  97 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 97 178 (accept_3_3 74 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 97 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 73 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 97 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 72 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 97 178 (accept_3_3 71 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  97 178 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 97 178 (accept_3_3 68 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 97 178
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 97 178 (accept_3_3 65 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  97 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 97 178 (accept_3_3 62 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 97 178 (Polychromatic418967fa.accept_17_10_12_8_1_2748 61 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 97 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 97 178 (accept_3_3 59 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  97 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 97 178 (accept_3_3 56 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 97 178
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 97 178 (accept_3_3 53 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  97 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 97 178 (accept_3_3 50 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 97 178 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 97 178
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 97 178 (accept_3_3 47 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  97 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 178 (accept_3_3 44 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 178
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 178 (accept_3_3 41 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 178 (accept_3_3 38 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 178
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 178 (accept_3_3 35 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 178 (Polychromatic418967fa.accept_23_11_5_17_1_10034 34 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 178 (accept_3_3 32 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 178 (accept_3_3 29 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 178 (accept_3_3 26 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 178
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 24 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 178 (accept_3_3 23 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 178 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 178 (accept_3_3 20 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 178 (accept_3_3 17 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 178 (accept_3_3 14 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 178 (Polychromatic418967fa.accept_19_13_2_7_1_8738 13 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 178
  (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 178 (accept_3_3 11 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 178 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 178 (accept_3_3 8 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 97 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 178
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 6 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 178 (accept_3_3 5 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 97 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 97 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 178 (accept_3_3 2 97 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 178 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 97 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 96 178 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 96 178 2 41 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 96 178 (Polychromatic418967fa.accept_13_3_5_9_1_5285 81 96 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 96 178 2 40 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 96 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 79 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 96 178 2 39 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 96 178 (accept_3_3 77 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 96
  178 2 38 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  96 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 75 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 96 178 2 37 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 96 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 96 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 96 178 2 36 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 96 178 (accept_3_3 71 96 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 96 178 2 35 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 96 178
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 96 178 2 34 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 96 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96 178 2 33 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 96 178 (accept_3_3 65 96 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 96 178 2 32 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 96 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 96 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 178 2 31 48 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 178
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 61 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 96 178 2 30 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 96 178 (accept_3_3 59 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 96
  178 2 29 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  96 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 96 178 2 28 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 96 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 96 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 178 2 27 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 178 (accept_3_3 53 96 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 178 2 26 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 178 2 25 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 96 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 178 2 24 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 178 (accept_3_3 47 96 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 178 2 23 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 178 (Polychromatic418967fa.accept_20_5_16_18_1_10033 45 96
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 178 2 22 48 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 178 2 21 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 178 (accept_3_3 41 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96
  178 2 20 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  96 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 96 178 2 19 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 96 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 96 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 178 2 18 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 178 (accept_3_3 35 96 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 178 2 17 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 178
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 178 2 16 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 96 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 178 2 15 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 178 (accept_3_3 29 96 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 178 2 14 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 96 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 178 2 13 48 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 178
  (Polychromatic418967fa.accept_19_6_1_7_1_5872 25 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 178 2 12 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 178 (accept_3_3 23 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  178 2 11 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 178 2 10 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 96 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 96 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 178 2 9 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 178 (accept_3_3 17 96 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 178 2 8 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 96 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 178 2 7 48 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 178 2 6 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 178 (accept_3_3 11 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  178 2 5 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 178 2 4 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 178 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 96 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 178 2 3 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 178 (accept_3_3 5 96 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 178 2 2 48 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 96 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 178 2 1 48 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 96 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 95
  178 (Eq.refl Bool.true) (allA_of_3_1 84 95 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 94 178 (Eq.refl
  Bool.true) (allA_succ_of_gcd 84 94 178 2 42 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 94 178 (accept_3_3 83 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 94 178 2 41 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 81 94 178 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 94 178 2 40 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 94 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 79
  94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 94 178 2 39 47 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 94 178 (accept_3_3 77
  94 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 94 178 2 38 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 94 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 94 178 2 37 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 94 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 94 178 2 36 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 94 178 (accept_3_3 71 94 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 94 178 2 35 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 94 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 94 178 2 34 47 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 94 178
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 67 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 94 178 2 33 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 94 178 (accept_3_3 65 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 94
  178 2 32 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  94 178 (Polychromatic418967fa.accept_19_6_18_7_1_10032 63 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 94 178 2 31 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 94 178 (Polychromatic418967fa.accept_18_7_4_16_1_2299 61 94 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 94 178 2 30 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 94 178 (accept_3_3 59 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 94 178 2 29 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 94 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 94 178 2 28 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 94 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 94 178 2 27 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 94 178 (accept_3_3 53 94 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94 178 2 26 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 94 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 94 178 2 25 47 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 178 2 24 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 94 178 (accept_3_3 47 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94
  178 2 23 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  94 178 (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 94 178 2 22 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 94 178 (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 94 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 178 2 21 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 178 (accept_3_3 41 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 178 2 20 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 94 178 2 19 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 94 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 178 2 18 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 178 (accept_3_3 35 94 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 178 2 17 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 178 2 16 47 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 178
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 178 2 15 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 178 (accept_3_3 29 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94
  178 2 14 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  94 178 (Polychromatic418967fa.accept_19_8_18_7_1_3143 27 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 94 178 2 13 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 94 178 (Polychromatic418967fa.accept_13_12_3_9_1_4341 25 94 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 178 2 12 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 178 (accept_3_3 23 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 178 2 11 47 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 178 2 10 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 178 2 9 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 178 (accept_3_3 17 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 178 2 8 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 94 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 178 2 7 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 178
  (Polychromatic418967fa.accept_25_13_19_3_1_10031 13 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 94 178 2 6 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 94 178 (accept_3_3 11 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 94 178 2 5 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 94 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 94 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 178 2 4 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 178 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 178 2 3 47 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 178 (accept_3_3 5 94 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 178 2 2 47 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 94
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 178 2 1 47 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 178
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 94 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 94 178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  93 178 (Eq.refl Bool.true) (allA_succ_of_accept 85 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 93 178
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 84 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 93 178 (accept_3_3 83 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  93 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 82 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 93 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 81 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 93 178 (accept_3_3 80 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 93 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 93 178 (accept_3_3 77 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  93 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 93 178 (accept_3_3 74 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 93 178
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 93 178 (accept_3_3 71 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  93 178 (Polychromatic418967fa.accept_13_5_2_9_1_1195 70 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 93 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 178 (accept_3_3 68 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 178
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 66 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 93 178 (accept_3_3 65 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  93 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 178 (accept_3_3 62 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 93 178 (accept_3_3 59 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  93 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 93 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 178 (accept_3_3 56 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 178 (accept_3_3 53 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  93 178 (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 178 (accept_3_3 50 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 178 (accept_3_3 47 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 178 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 178 (accept_3_3 44 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 178 (accept_3_3 41 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 178 (accept_3_3 38 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 178 (accept_3_3 35 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 178 (accept_3_3 32 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 178
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 178 (accept_3_3 29 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 178 (accept_3_3 26 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 178 (accept_3_3 23 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 178 (accept_3_3 20 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 178 (accept_3_3 17 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 178 (accept_3_3 14 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 178 (accept_3_3 11 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 178 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 178 (accept_3_3 8 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 93 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 178 (accept_3_3 5 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 93 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 93 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 178 (accept_3_3 2 93 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 93 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 92 178
  (Eq.refl Bool.true) (allA_of_3_1 87 92 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 91 178 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 91 178 (accept_3_3 86 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 91 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 91 178 (accept_3_3 83 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  91 178 (Polychromatic418967fa.accept_17_14_6_8_1_7688 82 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 91 178 (accept_3_3 80 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 91 178 (Polychromatic418967fa.accept_10_9_1_8_1_755 79 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 91 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 91 178 (accept_3_3 77 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  91 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 91 178 (accept_3_3 74 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 91 178
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 72 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 91 178 (accept_3_3 71 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  91 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 70 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 91 178 (accept_3_3 68 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 91 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 91 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 91 178 (accept_3_3 65 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  91 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 91 178 (accept_3_3 62 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 91 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 91 178 (accept_3_3 59 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  91 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 91 178 (accept_3_3 56 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 91 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 91 178
  (Polychromatic418967fa.accept_16_6_11_2_1_6485 54 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 178 (accept_3_3 53 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 178 (accept_3_3 50 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 178 (accept_3_3 47 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 178 (Polychromatic418967fa.accept_14_4_7_10_1_3888 46 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 178 (accept_3_3 44 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 178 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 178 (accept_3_3 41 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 178 (accept_3_3 38 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 178
  (Polychromatic418967fa.accept_19_17_15_7_1_10030 36 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 91 178 (accept_3_3 35 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 91 178 (Polychromatic418967fa.accept_11_1_3_2_1_1090 34 91 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 91 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 178 (accept_3_3 32 91 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 31
  91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 178 (accept_3_3 29 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 178 (accept_3_3 26 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 178 (accept_3_3 23 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 178 (accept_3_3 20 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 178 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 178
  (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 178 (accept_3_3 17 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 178 (accept_3_3 14 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 178 (accept_3_3 11 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 178 (accept_3_3 8 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 178 (Polychromatic418967fa.accept_16_7_11_2_1_3117 7 91 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 178 (accept_3_3 5 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 91 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 91 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 178 (accept_3_3 2 91 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 91 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 91 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 90 178
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 90 178 2 44 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 90 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 87 90 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 90 178 2 43 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 90 178
  (Polychromatic418967fa.accept_20_5_10_18_1_5622 85 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 90 178 2 42 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 83 90 178 (accept_3_3 83 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 90
  178 2 41 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81
  90 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 90 178 2 40 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 90 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 90 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 90 178 2 39 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 90 178 (accept_3_3 77 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 90 178 2 38 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 90 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 75 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 90 178 2 37 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 90 178 (Polychromatic418967fa.accept_13_8_12_9_1_1168 73 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90 178 2 36 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 90 178 (accept_3_3 71 90 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 90 178 2 35 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 90 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 178 2 34 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 90 178 2 33 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 90 178 (accept_3_3 65 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 90
  178 2 32 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  90 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 90 178 2 31 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 90 178 (Polychromatic418967fa.accept_19_4_14_7_1_5863 61 90 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 178 2 30 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 178 (accept_3_3 59 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 178 2 29 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 178 2 28 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 90 178 (Polychromatic418967fa.accept_13_3_12_9_1_1193 55 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 178 2 27 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 178 (accept_3_3 53 90 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 178 2 26 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 90 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 178 2 25 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 178
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 49 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 90 178 2 24 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 90 178 (accept_3_3 47 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90
  178 2 23 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  90 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 90 178 2 22 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 90 178 (Polychromatic418967fa.accept_23_20_21_17_1_10029 43 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 178 2 21 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 178 (accept_3_3 41
  90 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 178 2 20 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 178 2 19 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90 178 2 18 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 90 178 (accept_3_3 35 90 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 178 2 17 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 90 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 178 2 16 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 178
  (Polychromatic418967fa.accept_14_3_6_10_1_752 31 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 90 178 2 15 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 90 178 (accept_3_3 29 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90
  178 2 14 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  90 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 90 178 2 13 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 90 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 90 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 178 2 12 45 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 178 (accept_3_3 23 90 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 178 2 11 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 178 2 10 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 178 (Polychromatic418967fa.accept_23_19_21_17_1_4957 19 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 178 2 9 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 90 178 (accept_3_3 17 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 90 178 2 8 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 90 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 90 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 178 2 7 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 178 (Polychromatic418967fa.accept_17_13_5_8_1_896
  13 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 178 2 6 45 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 178 (accept_3_3 11
  90 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 178 2 5 45 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 178 2 4 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 178 (Polychromatic418967fa.accept_20_7_10_18_1_10001 7 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 178 2 3 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 178 (accept_3_3 5 90 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 178 2 2 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 90 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 178 2 1 45 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 178 (Polychromatic418967fa.accept_27_1_9_16_1_10028
  1 90 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 89 178
  (allA_of_3_1 89 89 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 88 178 (allA_succ_of_accept 87 88 178
  (Polychromatic418967fa.accept_19_11_12_7_1_3188 87 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 88 178 2 43 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 85 88 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 85 88 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 88 178 2 42 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 88 178 (accept_3_3 83 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 82 88 178 2 41 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 88 178 (Polychromatic418967fa.accept_17_13_3_8_1_6310 81 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 88 178 2 40 44 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 88 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 88 178 2 39 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 88 178 (accept_3_3 77 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 88
  178 2 38 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  88 178 (Polychromatic418967fa.accept_19_18_12_7_1_4432 75 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 88 178 2 37 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 88 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 73 88 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 88 178 2 36 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 88 178 (accept_3_3 71 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 88 178 2 35 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 88 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 88 178 2 34 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 88 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 67 88 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 88 178 2 33 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 88 178 (accept_3_3 65 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 88 178 2 32 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 88 178 (Polychromatic418967fa.accept_14_7_4_10_1_1351 63 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 88 178 2 31 44 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 88 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 88 178 2 30 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 88 178 (accept_3_3 59 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 88
  178 2 29 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  88 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 88 178 2 28 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 88 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 88 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 88 178 2 27 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 88 178 (accept_3_3 53 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88 178 2 26 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 88 178
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 88 178 2 25 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 88 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 88 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 178 2 24 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 178 (accept_3_3 47 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 178 2 23 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 178 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 178 2 22 44 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 178 2 21 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 88 178 (accept_3_3 41 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88
  178 2 20 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  88 178 (Polychromatic418967fa.accept_17_5_3_8_1_1697 39 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 88 178 2 19 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 88 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 88 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 178 2 18 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 178 (accept_3_3 35 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 178 2 17 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 88 178
  (Polychromatic418967fa.accept_19_14_12_7_1_10027 33 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 178 2 16 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 88 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 88 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 178 2 15 44 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 178 (accept_3_3 29 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 178 2 14 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 88 178 2 13 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 88 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 88 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 178 2 12 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 178 (accept_3_3 23 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 178 2 11 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 178 (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 88 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 88 178 2 10 44 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 88 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 88 178 2 9 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 88 178 (accept_3_3 17 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88
  178 2 8 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  88 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 88 178 2 7 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 88 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 88 178 2 6 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 88 178 (accept_3_3 11 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88 178 2 5 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 88 178 (Polychromatic418967fa.accept_26_9_10_22_1_10026 9 88 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 88 178 2 4 44 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 88 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 88 178 2 3 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 88 178 (accept_3_3 5 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 178
  2 2 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 88
  178 (Polychromatic418967fa.accept_19_3_12_7_1_10004 3 88 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 88 178 2 1 44 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 88 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 88 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 88
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 87 178
  (allA_succ_of_accept 86 87 178 (accept_3_3 86 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 87 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 87 178 (accept_3_3 83 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 87 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 87 178 (accept_3_3 80 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  87 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 87 178 (Polychromatic418967fa.accept_11_1_10_2_1_58 78 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 87 178 (accept_3_3 77 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 87 178 (accept_3_3 74 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 87 178 (Polychromatic418967fa.accept_19_15_11_7_1_8711 72 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 87 178 (accept_3_3 71 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 178 (Polychromatic418967fa.accept_15_10_12_13_1_2585 70 87
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 87 178 (accept_3_3 68 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  87 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 87 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 87 178 (accept_3_3 65 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 178
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 63 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 87 178 (accept_3_3 62 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 87 178 (Polychromatic418967fa.accept_16_12_7_2_1_4159 60 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 178 (accept_3_3 59 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 87 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 178 (accept_3_3 56 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 178 (accept_3_3 53 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 178 (Polychromatic418967fa.accept_19_14_11_7_1_7236 52 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 178
  (Polychromatic418967fa.accept_19_13_11_7_1_4451 51 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 178 (accept_3_3 50 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 178 (accept_3_3 47 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 178 (accept_3_3 44 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 178 (accept_3_3 41 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 178 (accept_3_3 38 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 178 (Polychromatic418967fa.accept_21_15_3_10_1_8533 36 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 178 (accept_3_3 35 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 178 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 87 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 178 (accept_3_3 32 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 178 (accept_3_3 29 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 178
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 178 (accept_3_3 26 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 178 (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 178 (accept_3_3 23 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 87 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 178 (accept_3_3 20 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 178 (accept_3_3 17 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 178 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 178
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 178 (accept_3_3 14 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 178 (accept_3_3 11 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 87 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 178 (accept_3_3 8 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 87 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 178 (accept_3_3 5 87 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 87 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  87 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 178 (accept_3_3 2 87 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 87
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 86 178
  (allA_of_3_1 86 86 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 85 178 (allA_succ_of_accept 84 85 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 85 178 (accept_3_3 83 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82
  85 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 85 178 (accept_3_3 80 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 85 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 85 178 (accept_3_3 77 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  85 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 85 178 (accept_3_3 74 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 85 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 85 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 72 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 85 178 (accept_3_3 71 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  85 178 (Polychromatic418967fa.accept_19_13_9_7_1_2038 70 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 85 178 (accept_3_3 68 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 85 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 85 178 (accept_3_3 65 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  85 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 178 (accept_3_3 62 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 85 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 178 (accept_3_3 59 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 178 (accept_3_3 56 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 178 (accept_3_3 53 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 178 (accept_3_3 50 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 178 (accept_3_3 47 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 178 (accept_3_3 44 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 178 (accept_3_3 41 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 178 (accept_3_3 38 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 178
  (Polychromatic418967fa.accept_19_17_9_7_1_3171 36 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 178 (accept_3_3 35 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 178 (Polychromatic418967fa.accept_13_8_7_9_1_611 34 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 178 (accept_3_3 32 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 178 (accept_3_3 29 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 178 (accept_3_3 26 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 178 (accept_3_3 23 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 178 (accept_3_3 20 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 178 (accept_3_3 17 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 178 (accept_3_3 14 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 178 (accept_3_3 11 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 178 (accept_3_3 8 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 85 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 178 (accept_3_3 5 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 85 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 85 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 85 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 178 (accept_3_3 2 85 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 85 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 85 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 84 178
  (allA_succ_of_accept 83 84 178 (accept_3_3 83 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 84
  178 2 41 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81
  84 178 (Polychromatic418967fa.accept_13_3_6_9_1_1150 81 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 84 178 2 40 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 84 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 79 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 84 178 2 39 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 84 178 (accept_3_3 77 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 178 2 38 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 178
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 75 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 178 2 37 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 84 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84 178 2 36 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 84 178 (accept_3_3 71 84 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 84 178 2 35 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 84 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 178 2 34 42 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 84 178 2 33 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 84 178 (accept_3_3 65 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 84
  178 2 32 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  84 178 (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 84 178 2 31 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 84 178 (Polychromatic418967fa.accept_26_9_6_22_1_10025 61 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 178 2 30 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 178 (accept_3_3 59 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 178 2 29 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 178
  (Polychromatic418967fa.accept_22_13_18_2_1_10024 57 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 84 178 2 28 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 84 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 178 2 27 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 178 (accept_3_3 53 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 178 2 26 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 178 2 25 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 84 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 84 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 178 2 24 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 178 (accept_3_3 47 84 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 178 2 23 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 178 (Polychromatic418967fa.accept_18_9_12_16_1_7323 45 84
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 178 2 22 42 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 178
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 43 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 178 2 21 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 178 (accept_3_3 41 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84
  178 2 20 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  84 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 84 178 2 19 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 84 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 178 2 18 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 178 (accept_3_3 35 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 178 2 17 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 84 178 2 16 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 84 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 178 2 15 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 178 (accept_3_3 29 84 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 178 2 14 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 178 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 178 2 13 42 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 178
  (Polychromatic418967fa.accept_19_6_8_7_1_10023 25 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 178 2 12 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 178 (accept_3_3 23 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84
  178 2 11 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  84 178 (Polychromatic418967fa.accept_23_21_15_17_1_10022 21 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 84 178 2 10 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 84 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 178 2 9 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 178 (accept_3_3 17 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 178 2 8 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 84 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 178 2 7 42 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 178
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 84 178 2 6 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 84 178 (accept_3_3 11 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84
  178 2 5 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  84 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 84 178 2 4 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 84 178 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 84 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 178 2 3 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84 178 (accept_3_3 5 84 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 178 2 2 42 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 84 178 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 84 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 178 2 1 42 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 84 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 83 178
  (allA_of_3_1 83 83 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 82 178 (allA_succ_of_accept 81 82 178
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 81 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 82 178 2 40 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 82 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 82 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 82 178 2 39 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 82 178 (accept_3_3 77 82 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 76 82 178 2 38 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 82 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 82 178 2 37 41 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 82 178
  (Polychromatic418967fa.accept_13_8_4_9_1_1145 73 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 82 178 2 36 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 82 178 (accept_3_3 71 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 82
  178 2 35 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  82 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 82 178 2 34 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 82 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 82 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 82 178 2 33 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 82 178 (accept_3_3 65 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82 178 2 32 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 82 178
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 82 178 2 31 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 82 178 (Polychromatic418967fa.accept_14_5_12_10_1_2985 61 82 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 178 2 30 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 178 (accept_3_3 59 82 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 178 2 29 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 82 178 2 28 41 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 82 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 82 178 2 27 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 82 178 (accept_3_3 53 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82
  178 2 26 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  82 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 82 178 2 25 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 82 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 82 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 82 178 2 24 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 82 178 (accept_3_3 47 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82 178 2 23 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 82 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 82 178 2 22 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 82 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 82 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 178 2 21 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 178 (accept_3_3 41 82 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 178 2 20 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 82 178 2 19 41 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 82 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 82 178 2 18 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 82 178 (accept_3_3 35 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82
  178 2 17 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  82 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 82 178 2 16 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 82 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 82 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 82 178 2 15 41 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 82 178 (accept_3_3 29 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82 178 2 14 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 82 178
  (Polychromatic418967fa.accept_19_8_6_7_1_7216 27 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 82 178 2 13 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 82 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 82 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 178 2 12 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 178 (accept_3_3 23 82 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 178 2 11 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 82 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 82 178 2 10 41 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 82 178
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 82 178 2 9 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 82 178 (accept_3_3 17 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 82
  178 2 8 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  82 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 82 178 2 7 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 82 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 82 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 178 2 6 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 178 (accept_3_3 11 82 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 178 2 5 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 82 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 82 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 82 178 2 4 41 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 82 178
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 82 178 2 3 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 82 178 (accept_3_3 5 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 82 178
  2 2 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 82
  178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 82 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 82 178 2 1 41 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 82 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 82 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 82
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 81 178
  (allA_succ_of_accept 80 81 178 (accept_3_3 80 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79
  81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 81 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 81 178 (accept_3_3 77 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 81 178 (accept_3_3 74 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73
  81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 81 178 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 81 178 (accept_3_3 71 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 178 (Polychromatic418967fa.accept_13_5_3_9_1_1189 70 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 81 178 (accept_3_3 68 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 81 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 178 (accept_3_3 65 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 178 (accept_3_3 62 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 178 (Polychromatic418967fa.accept_13_8_3_9_1_5269 60 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 178 (accept_3_3 59 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 178 (Polychromatic418967fa.accept_13_6_3_9_1_1827 58 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 178 (accept_3_3 56 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 178 (accept_3_3 53 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 178 (Polychromatic418967fa.accept_15_7_6_13_1_936 52 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 178 (accept_3_3 50 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 178 (accept_3_3 47 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 178 (Polychromatic418967fa.accept_13_7_3_9_1_1142 46 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 178
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 45 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 178 (accept_3_3 44 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 178 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 178 (accept_3_3 41 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 178 (Polychromatic418967fa.accept_19_2_5_7_1_10021 40 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 178 (accept_3_3 38 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 178 (accept_3_3 35 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 178
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 178 (accept_3_3 32 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 178 (accept_3_3 29 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 178 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 178 (accept_3_3 26 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 178 (Polychromatic418967fa.accept_21_3_18_10_1_10020 24 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 178 (accept_3_3 23 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 81 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 178
  (Polychromatic418967fa.accept_13_8_3_9_1_5269 21 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 178 (accept_3_3 20 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 178 (accept_3_3 17 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 178 (Polychromatic418967fa.accept_20_16_1_18_1_5617 16 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 178 (accept_3_3 14 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 178 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 178 (accept_3_3 11 81 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 178 (Polychromatic418967fa.accept_19_10_5_7_1_10007 10 81
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 178
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 178 (accept_3_3 8 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 81 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 178 (accept_3_3 5 81 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 178 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 81 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 178 (accept_3_3 2 81 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 178 (allA_of_3_1 80
  80 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 79 178 (allA_succ_of_accept 78 79 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 78 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 79 178 (accept_3_3 77 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76
  79 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 79 178 (accept_3_3 74 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 79 178
  (Polychromatic418967fa.accept_19_15_3_7_1_5875 72 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 79 178 (accept_3_3 71 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  79 178 (Polychromatic418967fa.accept_13_5_1_9_1_618 70 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 178 (accept_3_3 68 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 79 178 (Polychromatic418967fa.accept_10_7_9_8_1_1135 67 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 178
  (Polychromatic418967fa.accept_15_6_4_13_1_403 66 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 79 178 (accept_3_3 65 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  79 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 178 (accept_3_3 62 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 79 178
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 79 178 (accept_3_3 59 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  79 178 (Polychromatic418967fa.accept_13_6_1_9_1_619 58 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 178 (accept_3_3 56 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 79 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 79 178 (accept_3_3 53 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  79 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 178 (accept_3_3 50 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 79 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 79 178 (accept_3_3 47 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  79 178 (Polychromatic418967fa.accept_21_4_16_10_1_10019 46 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 178 (accept_3_3 44 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 79 178
  (Polychromatic418967fa.accept_19_4_3_7_1_5876 42 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 79 178 (accept_3_3 41 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  79 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 178 (accept_3_3 38 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 79 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 79 178 (accept_3_3 35 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  79 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 178 (accept_3_3 32 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 178 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 79 178
  (Polychromatic418967fa.accept_21_9_16_10_1_5371 30 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 79 178 (accept_3_3 29 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  79 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 79 178 (accept_3_3 26 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 79 178
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 79 178 (accept_3_3 23 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  79 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 79 178 (accept_3_3 20 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 79 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 79 178
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 79 178 (accept_3_3 17 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  79 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 79 178 (accept_3_3 14 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 79 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 79 178 (accept_3_3 11 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  79 178 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 79 178 (accept_3_3 8 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 79 178 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 79 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 79 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 79 178 (accept_3_3 5 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 79
  178 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 79 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 79 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 178 (accept_3_3 2 79 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 79 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 79 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 78 178
  (allA_succ_of_accept 77 78 178 (accept_3_3 77 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78
  178 2 38 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75
  78 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 78 178 2 37 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 78 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 78 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 178 2 36 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 178 (accept_3_3 71 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 78 178 2 35 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 78 178
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 69 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 78 178 2 34 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 78 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 178 2 33 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 178 (accept_3_3 65 78 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 178 2 32 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 178 2 31 39 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 178 2 30 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 178 (accept_3_3 59 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78
  178 2 29 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  78 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 78 178 2 28 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 78 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 78 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 178 2 27 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 178 (accept_3_3 53 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 178 2 26 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 178 2 25 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 78 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 178 2 24 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 178 (accept_3_3 47 78 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 178 2 23 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 178 2 22 39 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 178
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 178 2 21 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 178 (accept_3_3 41 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78
  178 2 20 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  78 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 78 178 2 19 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 78 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 78 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 178 2 18 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 178 (accept_3_3 35 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 178 2 17 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 178 2 16 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 78 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 178 2 15 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 178 (accept_3_3 29 78 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 178 2 14 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 178 2 13 39 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 78 178 2 12 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 78 178 (accept_3_3 23 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78
  178 2 11 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  78 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 78 178 2 10 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 78 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 78 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 178 2 9 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 178 (accept_3_3 17 78 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 178 2 8 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 78 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 178 2 7 39 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 178 2 6 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 178 (accept_3_3 11 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78
  178 2 5 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  78 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 78 178 2 4 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 78 178 (Polychromatic418967fa.accept_21_7_15_10_1_1368 7 78 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 178 2 3 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 178 (accept_3_3 5 78 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 178 2 2 39 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 78 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 78 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 178 2 1 39 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 78 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 78 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 178
  (allA_of_3_1 77 77 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 76 178 (allA_succ_of_accept 75 76 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 75 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 76 178 2 37 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 76 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 76 178 2 36 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 76 178 (accept_3_3 71 76 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76 178 2 35 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 76 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 76 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 76 178 2 34 38 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 76 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 76 178 2 33 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 76 178 (accept_3_3 65 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76
  178 2 32 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  76 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 76 178 2 31 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 76 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 61 76 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 178 2 30 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 178 (accept_3_3 59 76 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 178 2 29 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 76 178 2 28 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 76 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 76 178 2 27 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 76 178 (accept_3_3 53 76 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76 178 2 26 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 76 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 76 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 76 178 2 25 38 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 76 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 76 178 2 24 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 76 178 (accept_3_3 47 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76
  178 2 23 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  76 178 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 76 178 2 22 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 76 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 76 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 178 2 21 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 178 (accept_3_3 41 76 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 178 2 20 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 76 178 2 19 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 76 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 76 178 2 18 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 76 178 (accept_3_3 35 76 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76 178 2 17 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 76 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 76 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 76 178 2 16 38 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 76 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 76 178 2 15 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 76 178 (accept_3_3 29 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76
  178 2 14 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  76 178 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 76 178 2 13 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 76 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 76 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 76 178 2 12 38 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 76 178 (accept_3_3 23 76 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76 178 2 11 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 76 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 76 178 2 10 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 76 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 178 2 9 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 178 (accept_3_3 17 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 76 178 2 8 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 76 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 76 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 178 2 7 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  13 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 76 178 2 6 38 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 76 178 (accept_3_3 11
  76 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76 178 2 5 38 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 76 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 76 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 76 178 2 4 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 76 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 178 2 3 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 178 (accept_3_3 5 76 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 76 178 2 2 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 76 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 76 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 178 2 1 38 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 76
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 75 178 (allA_succ_of_accept
  74 75 178 (accept_3_3 74 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 75 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 178 (accept_3_3 71 75 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 75 178 (Polychromatic418967fa.accept_11_4_9_2_1_259 70 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 69
  75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 178 (accept_3_3 68 75
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 178 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 178 (accept_3_3 65 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 178 (accept_3_3 62 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 178 (accept_3_3 59 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 178 (accept_3_3 56 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 54 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 178 (accept_3_3 53 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 178 (accept_3_3 50 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 178
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 178 (accept_3_3 47 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 178 (accept_3_3 44 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 178 (accept_3_3 41 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 178 (Polychromatic418967fa.accept_16_7_11_2_1_3117 39 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 178 (accept_3_3 38 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 75 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 178 (accept_3_3 35 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 178 (Polychromatic418967fa.accept_19_15_18_7_1_10018 34 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 178 (accept_3_3 32 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 178 (accept_3_3 29 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 178 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 178 (accept_3_3 26 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 178 (accept_3_3 23 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 178 (accept_3_3 20 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 178
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 178 (accept_3_3 17 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 178 (accept_3_3 14 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 178
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 178 (accept_3_3 11 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 178 (accept_3_3 8 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 178 (accept_3_3 5 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 75 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 75 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 178 (accept_3_3 2 75 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 75 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 178 (allA_of_3_1 74 74
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 178 (allA_succ_of_accept 72 73 178
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 178 (accept_3_3 71 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 178 (Polychromatic418967fa.accept_16_6_9_2_1_6518 70 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 178 (accept_3_3 68 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 178 (accept_3_3 65 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 178 (Polychromatic418967fa.accept_11_9_7_2_1_1068 64 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 178 (accept_3_3 62 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 61 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 178 (accept_3_3 59 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 178 (accept_3_3 56 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 178
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 54 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 178 (accept_3_3 53 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 178 (accept_3_3 50 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 178 (accept_3_3 47 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 178 (accept_3_3 44 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 178 (accept_3_3 41 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 178 (accept_3_3 38 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 178 (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 178
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 178 (accept_3_3 35 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 178 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 178 (accept_3_3 32 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 178 (accept_3_3 29 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 178 (accept_3_3 26 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 178 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 178 (accept_3_3 23 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 178 (accept_3_3 20 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 178
  (Polychromatic418967fa.accept_22_18_7_2_1_10017 18 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 178 (accept_3_3 17 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 178 (accept_3_3 14 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 178 (accept_3_3 11 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 178 (accept_3_3 8 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 73 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 178 (accept_3_3 5 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 73 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 73 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 178 (accept_3_3 2 73 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 73 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 178 (allA_succ_of_accept 71
  72 178 (accept_3_3 71 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 178 2 35 36 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 178 2 34 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 178 (Polychromatic418967fa.accept_13_2_7_9_1_2616 67 72 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 178 2 33 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 178 (accept_3_3 65 72 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 178 2 32 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 178 (Polychromatic418967fa.accept_13_11_7_9_1_612 63 72 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 178 2 31 36 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 178 2 30 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 178 (accept_3_3 59 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  178 2 29 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 178 2 28 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 72 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 178 2 27 36 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 178 (accept_3_3 53 72 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 178 2 26 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 178
  (Polychromatic418967fa.accept_19_13_15_7_1_5843 51 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 178 2 25 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 178 (Polychromatic418967fa.accept_19_11_15_7_1_3177 49 72 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 178 2 24 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 178 (accept_3_3 47 72 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 178 2 23 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 72 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 178 2 22 36 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 178 2 21 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 178 (accept_3_3 41 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  178 2 20 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 178 (Polychromatic418967fa.accept_21_18_9_10_1_2571 39 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 178 2 19 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 178 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 72 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 178 2 18 36 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 178 (accept_3_3 35 72 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 178 2 17 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 178 2 16 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 178 (Polychromatic418967fa.accept_15_1_12_13_1_944 31 72 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 178 2 15 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 178 (accept_3_3 29 72 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 178 2 14 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 178 2 13 36 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 72 178 2 12 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 72 178 (accept_3_3 23 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72
  178 2 11 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  72 178 (Polychromatic418967fa.accept_13_8_7_9_1_611 21 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 72 178 2 10 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 72 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 72 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 178 2 9 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 178 (accept_3_3 17 72 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 178 2 8 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 178 2 7 36 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 72 178 2 6 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 72 178 (accept_3_3 11 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72
  178 2 5 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  72 178 (Polychromatic418967fa.accept_23_9_3_17_1_8428 9 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 72 178 2 4 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 72 178 (Polychromatic418967fa.accept_17_7_4_8_1_7678 7 72 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 178 2 3 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 178 (accept_3_3 5 72 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 178 2 2 36 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 72 178 (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 72 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 178 2 1 36 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 72 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 178
  (allA_of_3_1 71 71 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 178 (allA_succ_of_accept 69 70 178
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 69 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 178 2 34 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 178 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 70 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 178 2 33 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 178 (accept_3_3 65 70 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 178 2 32 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 178 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 70
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 178 2 31 35 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 178
  (Polychromatic418967fa.accept_11_6_4_2_1_599 61 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 178 2 30 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 178 (accept_3_3 59 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  178 2 29 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 178 (Polychromatic418967fa.accept_15_12_10_13_1_4497 57 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 178 2 28 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 70 178 (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 70 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 178 2 27 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 178 (accept_3_3 53 70 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 178 2 26 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 178
  (Polychromatic418967fa.accept_16_3_6_2_1_4157 51 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 178 2 25 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 178 (Polychromatic418967fa.accept_15_4_10_13_1_2565 49 70 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 178 2 24 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 178 (accept_3_3 47 70 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 178 2 23 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 178 (Polychromatic418967fa.accept_17_11_2_8_1_7569 45 70 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 178 2 22 35 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 178
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 43 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 178 2 21 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 178 (accept_3_3 41 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  178 2 20 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 178 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 178 2 19 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 178 (Polychromatic418967fa.accept_20_17_10_18_1_4150 37 70 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 178 2 18 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 178 (accept_3_3 35 70 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 178 2 17 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 178
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 33 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 178 2 16 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 178 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 70 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 178 2 15 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 178 (accept_3_3 29 70 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 178 2 14 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 178 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 70 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 178 2 13 35 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 178
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 178 2 12 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 178 (accept_3_3 23 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  178 2 11 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 178 (Polychromatic418967fa.accept_19_2_13_7_1_7211 21 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 178 2 10 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 70 178 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 70 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 178 2 9 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 178 (accept_3_3 17 70 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 178 2 8 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 178 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 70 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 178 2 7 35 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 178
  (Polychromatic418967fa.accept_21_13_7_10_1_8599 13 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 178 2 6 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 178 (accept_3_3 11 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  178 2 5 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 178 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 178 2 4 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 178 (Polychromatic418967fa.accept_20_7_10_18_1_10001 7 70 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 178 2 3 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 178 (accept_3_3 5 70 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 178 2 2 35 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 178 (Polychromatic418967fa.accept_13_3_5_9_1_5285 3 70 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 178 2 1 35 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 178
  (Polychromatic418967fa.accept_13_1_5_9_1_226 1 70 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 178
  (allA_succ_of_accept 68 69 178 (accept_3_3 68 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 178 (accept_3_3 65 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 178 (accept_3_3 62 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 178 (accept_3_3 59 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 178 (accept_3_3 56 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 178 (accept_3_3 53 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 178 (Polychromatic418967fa.accept_15_7_9_13_1_3451 52 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 178 (accept_3_3 50 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 178 (accept_3_3 47 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 178
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 178 (accept_3_3 44 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 178 (accept_3_3 41 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 178 (accept_3_3 38 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 178 (Polychromatic418967fa.accept_21_15_6_10_1_10016 36 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 178 (accept_3_3 35 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 69 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 178
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 33 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 178 (accept_3_3 32 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 178 (accept_3_3 29 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 178 (accept_3_3 26 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 178 (accept_3_3 23 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 178 (accept_3_3 20 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 178 (accept_3_3 17 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 178 (accept_3_3 14 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 178 (accept_3_3 11 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 69 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 178 (accept_3_3 8 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 69 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 69 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 178 (accept_3_3 5 69 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 69 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 178 (accept_3_3 2 69 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 178 (allA_of_3_1 68 68 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 178 (allA_succ_of_accept 66 67 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 178 (accept_3_3 65 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 178 (accept_3_3 62 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 178 (accept_3_3 59 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 178 (Polychromatic418967fa.accept_11_3_1_2_1_1063 58 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 178 (accept_3_3 56 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 178
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 178 (accept_3_3 53 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 178 (accept_3_3 50 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 178 (accept_3_3 47 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 178 (accept_3_3 44 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 178 (accept_3_3 41 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 178 (accept_3_3 38 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 178 (accept_3_3 35 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 178 (accept_3_3 32 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 178 (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 178 (accept_3_3 29 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 178 (accept_3_3 26 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 178 (accept_3_3 23 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 178 (accept_3_3 20 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 178
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 178 (accept_3_3 17 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 178 (accept_3_3 14 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 178 (accept_3_3 11 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 178 (accept_3_3 8 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 178 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 178 (accept_3_3 5 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  178 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 67 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 178 (accept_3_3 2 67 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 67 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 178 (allA_succ_of_accept 65 66
  178 (accept_3_3 65 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 178 2 32 33 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 178
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 178 2 31 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 178 (Polychromatic418967fa.accept_17_10_15_8_1_6324 61 66 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 178 2 30 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 178 (accept_3_3 59 66 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 178 2 29 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 66 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 178 2 28 33 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 178 2 27 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 178 (accept_3_3 53 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  178 2 26 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 178 2 25 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 66 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 178 2 24 33 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 178 (accept_3_3 47 66 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 178 2 23 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 178 2 22 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 66 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 178 2 21 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 178 (accept_3_3 41 66 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 178 2 20 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 66 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 178 2 19 33 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 178 2 18 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 178 (accept_3_3 35 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  178 2 17 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 178 2 16 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 66 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 178 2 15 33 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 178 (accept_3_3 29 66 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 178 2 14 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 178 2 13 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 178 (Polychromatic418967fa.accept_23_2_20_17_1_10015 25 66 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 178 2 12 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 178 (accept_3_3 23 66 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 178 2 11 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 66 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 178 2 10 33 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 178 2 9 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 178 (accept_3_3 17 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  178 2 8 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 178 2 7 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 66 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 178 2 6 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 178 (accept_3_3 11 66 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 178 2 5 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 66 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 178 2 4 33 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 178
  (Polychromatic418967fa.accept_15_7_6_13_1_936 7 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 178 2 3 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 178 (accept_3_3 5 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 178
  2 2 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 178 2 1 33 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 66 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 178 (allA_of_3_1 65 65 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 178 (allA_succ_of_accept 63 64 178
  (Polychromatic418967fa.accept_22_19_20_2_1_3578 63 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 178 2 31 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 64 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 64 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 178 2 30 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 178 (accept_3_3 59 64 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 178 2 29 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 64 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 178 2 28 32 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 178 2 27 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 64 178 (accept_3_3 53 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64
  178 2 26 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  64 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 64 178 2 25 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 64 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 64 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 178 2 24 32 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 178 (accept_3_3 47 64 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 178 2 23 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 178
  (Polychromatic418967fa.accept_21_3_1_10_1_10008 45 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 178 2 22 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 64 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 178 2 21 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 178 (accept_3_3 41 64 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 178 2 20 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 64 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 178 2 19 32 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 178 2 18 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 178 (accept_3_3 35 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  178 2 17 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 178 2 16 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 64 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 64 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 178 2 15 32 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 178 (accept_3_3 29 64 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 178 2 14 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 178
  (Polychromatic418967fa.accept_24_3_16_10_1_8350 27 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 64 178 2 13 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 64 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 64 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 64 178 2 12 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 64 178 (accept_3_3 23 64 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64 178 2 11 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 64 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 64 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 64 178 2 10 32 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 64 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 64 178 2 9 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 64 178 (accept_3_3 17 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64
  178 2 8 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  64 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 64 178 2 7 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 64 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 64 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 64 178 2 6 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 64 178 (accept_3_3 11 64 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64 178 2 5 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 64 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 64 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 64 178 2 4 32 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 64 178
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 64 178 2 3 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 64 178 (accept_3_3 5 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 178
  2 2 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 64
  178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 64 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 64 178 2 1 32 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 64 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 64 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 64 178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 63 178 (allA_succ_of_accept 62 63 178 (accept_3_3 62 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 63 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 63 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 63 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 178 (accept_3_3 59 63 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 178 (Polychromatic418967fa.accept_19_1_6_7_1_2019
  58 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 178 (accept_3_3 56 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 178 (accept_3_3 53 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 178 (Polychromatic418967fa.accept_19_14_6_7_1_7223 52 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 178
  (Polychromatic418967fa.accept_10_1_3_8_1_136 51 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 178 (accept_3_3 50 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 178 (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 178 (accept_3_3 47 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 63 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 178 (accept_3_3 44 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 178 (accept_3_3 41 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 178 (Polychromatic418967fa.accept_13_1_11_9_1_1857 40 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 178
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 178 (accept_3_3 38 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 178 (accept_3_3 35 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 178 (Polychromatic418967fa.accept_13_8_11_9_1_593 34 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 178 (accept_3_3 32 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 178 (accept_3_3 29 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 178 (Polychromatic418967fa.accept_13_2_11_9_1_591 28 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 178
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 178 (accept_3_3 26 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 178 (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 178 (accept_3_3 23 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 178 (Polychromatic418967fa.accept_17_5_12_8_1_6304 22 63
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 178 (accept_3_3 20 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 178 (accept_3_3 17 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 178
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 178 (accept_3_3 14 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 178 (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 178 (accept_3_3 11 63 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 178 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 63
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 178 (accept_3_3 8 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 178 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 178 (accept_3_3 5 63 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 178 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 63 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 178 (Polychromatic418967fa.accept_14_3_7_10_1_2146
  3 63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 178 (accept_3_3 2 63
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  63 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 178 (allA_of_3_1 62 62 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 178 (allA_succ_of_accept 60 61 178
  (Polychromatic418967fa.accept_19_3_4_7_1_987 60 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 178 (accept_3_3 59 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 178 (accept_3_3 56 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 178
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 178 (accept_3_3 53 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 178 (accept_3_3 50 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 178 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 178
  (Polychromatic418967fa.accept_11_4_6_2_1_51 48 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 178 (accept_3_3 47 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 178 (Polychromatic418967fa.accept_17_12_10_8_1_5039 46 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 178 (accept_3_3 44 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 178
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 42 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 178 (accept_3_3 41 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 178 (accept_3_3 38 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 178
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 178 (accept_3_3 35 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 178 (Polychromatic418967fa.accept_23_11_15_17_1_10014 34 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 178 (accept_3_3 32 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 178 (accept_3_3 29 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 178 (accept_3_3 26 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 178
  (Polychromatic418967fa.accept_25_24_11_3_1_10013 24 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 61 178 (accept_3_3 23 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 61 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 61 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 61 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 178 (accept_3_3 20 61 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 178
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 178 (accept_3_3 17 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 178 (accept_3_3 14 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 178 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 178
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 178 (accept_3_3 11 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 10 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 178 (accept_3_3 8 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 61 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 178
  (Polychromatic418967fa.accept_22_6_17_2_1_3518 6 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 178 (accept_3_3 5 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  178 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 61 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 61 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 178 (accept_3_3 2 61 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 61 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 178 (allA_succ_of_accept 59 60 178 (accept_3_3 59 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 178 2 29 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 178 2 28 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 55
  60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 178 2 27 30 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 178 (accept_3_3 53
  60 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 178 2 26 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 178
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 51 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 178 2 25 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 60 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 178 2 24 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 178 (accept_3_3 47 60 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 178 2 23 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 178 (Polychromatic418967fa.accept_17_11_9_8_1_5038 45 60 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 178 2 22 30 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 178 2 21 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 178 (accept_3_3 41 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  178 2 20 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 178 2 19 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 60 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 178 2 18 30 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 178 (accept_3_3 35 60 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 178 2 17 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 178
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 178 2 16 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 60 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 178 2 15 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 178 (accept_3_3 29 60 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 178 2 14 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 60 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 178 2 13 30 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 178
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 178 2 12 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 178 (accept_3_3 23 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60
  178 2 11 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  60 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 60 178 2 10 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 60 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 60 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 178 2 9 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 178 (accept_3_3 17 60 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 178 2 8 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 178 2 7 30 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 60 178 2 6 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 60 178 (accept_3_3 11 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  178 2 5 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 178 (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 60 178 2 4 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 60 178 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 60 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 178 2 3 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60 178 (accept_3_3 5 60 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 178 2 2 30 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 60 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 60 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 178 2 1 30 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 60 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 60 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 178 (allA_of_3_1 59 59 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 178 (allA_succ_of_accept 57 58 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 58 178 2 28 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 58 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 58 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 178 2 27 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 178 (accept_3_3 53 58 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 178 2 26 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 58 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 58 178 2 25 29 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 58 178
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 58 178 2 24 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 58 178 (accept_3_3 47 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58
  178 2 23 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  58 178 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 58 178 2 22 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 58 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 58 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 58 178 2 21 29 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 58 178 (accept_3_3 41 58 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58 178 2 20 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 58 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 58 178 2 19 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 58 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 58 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 178 2 18 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 178 (accept_3_3 35 58 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 178 2 17 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 58 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 58 178 2 16 29 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 58 178
  (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 58 178 2 15 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 58 178 (accept_3_3 29 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58
  178 2 14 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  58 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 58 178 2 13 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 58 178 (Polychromatic418967fa.accept_18_7_4_16_1_2299 25 58 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 58 178 2 12 29 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 58 178 (accept_3_3 23 58 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58 178 2 11 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 58 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 58 178 2 10 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 58 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 58 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 178 2 9 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 178 (accept_3_3 17 58 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 58 178 2 8 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 58 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 58 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 178 2 7 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 58 178 2 6 29 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 58 178 (accept_3_3 11
  58 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58 178 2 5 29 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 58 178
  (Polychromatic418967fa.accept_21_9_16_10_1_5371 9 58 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 58 178 2 4 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 58 178 (Polychromatic418967fa.accept_13_7_6_9_1_1831 7 58 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 178 2 3 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 178 (accept_3_3 5 58 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 58 178 2 2 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 58 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 58 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 178 2 1 29 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 58
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58
  178)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 178 (allA_succ_of_accept 56 57 178
  (accept_3_3 56 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 178 (accept_3_3 53 57 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 178 (Polychromatic418967fa.accept_22_8_13_2_1_10012 52 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 178 (accept_3_3 50 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 178 (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 178 (accept_3_3 47 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 57 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 178
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 178 (accept_3_3 44 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 178 (accept_3_3 41 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 178 (accept_3_3 38 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 178 (Polychromatic418967fa.accept_23_13_11_17_1_10011 36 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 178 (accept_3_3 35 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 178 (Polychromatic418967fa.accept_25_9_7_3_1_10010 34 57
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 178 (accept_3_3 32 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 178 (accept_3_3 29 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 178 (accept_3_3 26 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 178 (accept_3_3 23 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 178
  (Polychromatic418967fa.accept_20_1_17_18_1_1678 21 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 178 (accept_3_3 20 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 178 (accept_3_3 17 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 178 (accept_3_3 14 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 178 (accept_3_3 11 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 57 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 178 (accept_3_3 8 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 57 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 57 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 178 (accept_3_3 5 57 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 57 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 178 (accept_3_3 2 57 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 178 (allA_of_3_1 56 56 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 178 (allA_succ_of_accept 54 55 178
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 54 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 178 (accept_3_3 53 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 178 (accept_3_3 50 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 178 (accept_3_3 47 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 178 (accept_3_3 44 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 178 (accept_3_3 41 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 178 (accept_3_3 38 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 178
  (Polychromatic418967fa.accept_20_16_15_18_1_5605 36 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 55 178 (accept_3_3 35 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 55 178 (Polychromatic418967fa.accept_13_8_3_9_1_5269 34 55 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 55 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 178 (accept_3_3 32 55 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 31
  55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 178 (accept_3_3 29 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 178 (accept_3_3 26 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 178 (accept_3_3 23 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 178 (accept_3_3 20 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 178 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 178 (accept_3_3 17 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 178 (accept_3_3 14 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 178 (accept_3_3 11 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 178 (accept_3_3 8 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 178 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 55 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 178 (accept_3_3 5 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 55 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 178 (accept_3_3 2 55 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 55 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 178)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 178 (allA_succ_of_accept 53 54 178 (accept_3_3 53 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 178 2 26 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 178 2 25 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 49
  54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 178 2 24 27 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 178 (accept_3_3 47
  54 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 178 2 23 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 178
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 178 2 22 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 54 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54 178 2 21 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 54 178 (accept_3_3 41 54 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 178 2 20 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 54 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 54 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 178 2 19 27 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 54 178 2 18 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 54 178 (accept_3_3 35 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54
  178 2 17 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  54 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 54 178 2 16 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 54 178 (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 54 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 178 2 15 27 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 178 (accept_3_3 29 54 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 178 2 14 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 178 2 13 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 178 (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 54 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54 178 2 12 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 54 178 (accept_3_3 23 54 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 178 2 11 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 54 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 54 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 178 2 10 27 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 178
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 54 178 2 9 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 54 178 (accept_3_3 17 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54
  178 2 8 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  54 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 54 178 2 7 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 54 178 (Polychromatic418967fa.accept_17_13_3_8_1_6310 13 54 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 178 2 6 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 178 (accept_3_3 11 54 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 178 2 5 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 54 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 178 2 4 27 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 178
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 178 2 3 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 178 (accept_3_3 5 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 178
  2 2 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54
  178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 54 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 54 178 2 1 27 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 54 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 54 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54 178))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 53 178 (allA_of_3_1 53 53 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 178
  (allA_succ_of_accept 51 52 178 (Polychromatic418967fa.accept_15_6_7_13_1_1666 51 52 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 178 2 25 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 178 (Polychromatic418967fa.accept_11_5_8_2_1_588 49
  52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 178 2 24 26 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 178 (accept_3_3 47
  52 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 178 2 23 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 178 2 22 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 52 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 178 2 21 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 178 (accept_3_3 41 52 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 178 2 20 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 178 (Polychromatic418967fa.accept_15_9_7_13_1_1664 39 52 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 178 2 19 26 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 178
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 178 2 18 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 178 (accept_3_3 35 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  178 2 17 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 178 (Polychromatic418967fa.accept_22_11_8_2_1_8450 33 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 178 2 16 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 52 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 31 52 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 178 2 15 26 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 178 (accept_3_3 29 52 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 178 2 14 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 178
  (Polychromatic418967fa.accept_11_5_8_2_1_588 27 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 52 178 2 13 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 52 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 52 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 178 2 12 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 178 (accept_3_3 23 52 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 178 2 11 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 178 (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 52 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 178 2 10 26 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 178 2 9 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 178 (accept_3_3 17 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  178 2 8 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 178 2 7 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 13 52 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 178 2 6 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 178 (accept_3_3 11 52 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 178 2 5 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 178 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 52 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 178 2 4 26 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 178
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 178 2 3 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 178 (accept_3_3 5 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 178
  2 2 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  178 (Polychromatic418967fa.accept_19_3_14_7_1_7204 3 52 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 52 178 2 1 26 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 52 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 52 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 178))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 178 (allA_succ_of_accept 50 51 178 (accept_3_3 50 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 51 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 178 (accept_3_3 47 51 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 46
  51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 178 (accept_3_3 44 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 178 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 178 (accept_3_3 41 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 178 (accept_3_3 38 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 178 (accept_3_3 35 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 178 (accept_3_3 32 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 178 (accept_3_3 29 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 178 (accept_3_3 26 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 178 (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 178 (accept_3_3 23 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 51 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 178 (accept_3_3 20 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 178 (accept_3_3 17 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 178 (Polychromatic418967fa.accept_13_3_12_9_1_1193 16 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 178 (accept_3_3 14 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 178 (accept_3_3 11 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 51 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 178 (accept_3_3 8 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 178 (accept_3_3 5 51 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 51 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  51 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 178 (accept_3_3 2 51 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 51
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  178))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 178 (allA_of_3_1 50 50 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 178 (allA_succ_of_accept 48 49 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 49
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 178 (accept_3_3 47 49 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 46
  49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 178 (accept_3_3 44 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 178 (accept_3_3 41 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 178 (accept_3_3 38 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 178 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 178 (accept_3_3 35 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 178 (accept_3_3 32 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 178 (accept_3_3 29 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 178 (accept_3_3 26 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 178 (Polychromatic418967fa.accept_13_12_10_9_1_1166 25 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 178 (accept_3_3 23 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 178 (Polychromatic418967fa.accept_16_6_1_2_1_3129 22 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 178 (accept_3_3 20 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 178 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 178 (accept_3_3 17 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 49 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 178 (accept_3_3 14 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 178 (Polychromatic418967fa.accept_17_13_15_8_1_3860 13 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 178 (accept_3_3 11 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 49 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 178
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 178 (accept_3_3 8 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 49 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 49 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 178 (accept_3_3 5 49 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 49 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 49
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 178 (accept_3_3 2 49 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 49
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  178))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 178 (allA_succ_of_accept 47 48 178 (accept_3_3 47
  48 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 178 2 23 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 178
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 178 2 22 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 178 (Polychromatic418967fa.accept_19_5_10_7_1_5887 43 48 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 178 2 21 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 178 (accept_3_3 41 48 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 178 2 20 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 178 2 19 24 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 178
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 48 178 2 18 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 48 178 (accept_3_3 35 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 48
  178 2 17 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  48 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 48 178 2 16 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 48 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 48 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 178 2 15 24 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 178 (accept_3_3 29 48 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 178 2 14 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 178
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 178 2 13 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 48 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 178 2 12 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 178 (accept_3_3 23 48 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 178 2 11 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 178 (Polychromatic418967fa.accept_20_1_8_18_1_8648 21 48 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 178 2 10 24 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 178
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 178 2 9 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 178 (accept_3_3 17 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  178 2 8 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 178 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 178 2 7 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 48 178 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 48 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 178 2 6 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 178 (accept_3_3 11 48 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 178 2 5 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 48 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 178 2 4 24 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 178
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 178 2 3 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 178 (accept_3_3 5 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 178
  2 2 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48
  178 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 48 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 48 178 2 1 24 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 48 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 48 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 178)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 178 (allA_of_3_1 47 47 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 178 (allA_succ_of_accept 45 46
  178 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 178 2 22 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 46 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 178 2 21 23 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 178 (accept_3_3 41 46 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 178 2 20 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 178 2 19 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 178 (Polychromatic418967fa.accept_13_11_7_9_1_612 37 46 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 178 2 18 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 178 (accept_3_3 35 46 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 178 2 17 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 46 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 178 2 16 23 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 178
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 178 2 15 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 178 (accept_3_3 29 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  178 2 14 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 178 2 13 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 178 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 46 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 178 2 12 23 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 178 (accept_3_3 23 46 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 178 2 11 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 178 2 10 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 178 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 46 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 178 2 9 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 178 (accept_3_3 17 46 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 178 2 8 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 46 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 178 2 7 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 178 2 6 23 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 178 (accept_3_3 11
  46 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 178 2 5 23 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 178
  (Polychromatic418967fa.accept_19_9_8_7_1_2061 9 46 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 178 2 4 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 178 (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 46 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 178 2 3 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 178 (accept_3_3 5 46 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 178 2 2 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 46 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 178 2 1 23 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 46
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  178)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 178 (allA_succ_of_accept 44 45 178 (accept_3_3 44 45
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62
  43 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 178
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 178 (accept_3_3 41 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  45 178 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 178 (accept_3_3 38 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 178
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 178 (accept_3_3 35 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  45 178 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 178 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 178 (accept_3_3 32 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 45 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 45 178 (accept_3_3 29 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  45 178 (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 178 (accept_3_3 26 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 178
  (Polychromatic418967fa.accept_23_1_22_17_1_10009 24 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 178 (accept_3_3 23 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 178 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 45 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 178 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 178 (accept_3_3 20 45 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 45 178 (accept_3_3 17 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  45 178 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 178 (accept_3_3 14 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 178
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 178 (accept_3_3 11 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  45 178 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 45 178 (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 178 (accept_3_3 8 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 45 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 178 (accept_3_3 5 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45
  178 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 45 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 178 (accept_3_3 2 45 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 178)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 44 178 (allA_of_3_1 44 44 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 43 178
  (allA_succ_of_accept 42 43 178 (Polychromatic418967fa.accept_20_2_3_18_1_8645 42 43 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 178 (accept_3_3 41 43 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 43 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 178 (accept_3_3 38 43
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3
  37 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 178
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 178 (accept_3_3 35 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 178 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 178 (accept_3_3 32 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 178 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 43 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 178
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 178 (accept_3_3 29 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 178 (accept_3_3 26 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 43 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 178
  (Polychromatic418967fa.accept_21_3_1_10_1_10008 24 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 178 (accept_3_3 23 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 178 (Polychromatic418967fa.accept_16_6_11_2_1_6485 22 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 178 (accept_3_3 20 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 43 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 178
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 178 (accept_3_3 17 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 178 (accept_3_3 14 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 43 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 178 (accept_3_3 11 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 178 (Polychromatic418967fa.accept_19_10_5_7_1_10007 10 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 178 (accept_3_3 8 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 178 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 43 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 178
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 178 (accept_3_3 5 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 43 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 178 (accept_3_3 2 43 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 43 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 178))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 178
  (allA_succ_of_accept 41 42 178 (accept_3_3 41 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42
  178 2 20 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  42 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 42 178 2 19 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 42 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 42 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 178 2 18 21 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 178 (accept_3_3 35 42 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 178 2 17 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 178 2 16 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 178 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 42 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 178 2 15 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 178 (accept_3_3 29 42 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42 178 2 14 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 42 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 42 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 178 2 13 21 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 178
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 42 178 2 12 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 42 178 (accept_3_3 23 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42
  178 2 11 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  42 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 42 178 2 10 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 42 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 42 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 178 2 9 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 178 (accept_3_3 17 42 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 178 2 8 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 178 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 178 2 7 21 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 42 178 2 6 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 42 178 (accept_3_3 11 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42
  178 2 5 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  42 178 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 42 178 2 4 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 42 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 42 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 178 2 3 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 178 (accept_3_3 5 42 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 178 2 2 21 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 42 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 42 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 178 2 1 21 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 42 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 178)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 178 (allA_of_3_1 41 41 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 40 178 (allA_succ_of_accept 39 40 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 39 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 178 2 19 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 40 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 178 2 18 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 178 (accept_3_3 35 40 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40 178 2 17 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 40 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 40 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 178 2 16 20 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 178
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 178 2 15 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 178 (accept_3_3 29 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  178 2 14 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 178 (Polychromatic418967fa.accept_15_12_10_13_1_4497 27 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 178 2 13 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 40 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 178 2 12 20 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 178 (accept_3_3 23 40 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 178 2 11 20 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 40 178 2 10 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 40 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 40 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 178 2 9 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 178 (accept_3_3 17 40 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 40 178 2 8 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 40 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 40 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 178 2 7 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 178 (Polychromatic418967fa.accept_12_1_4_10_1_209
  13 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 178 2 6 20 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 178 (accept_3_3 11
  40 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 178 2 5 20 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 40 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 40 178 2 4 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 40 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 40 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 178 2 3 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 178 (accept_3_3 5 40 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 40 178 2 2 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 40 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 40 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 178 2 1 20 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 40
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40
  178)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 178 (allA_succ_of_accept 38 39 178 (accept_3_3 38 39 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 39 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 39 178 (accept_3_3 35 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  39 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 178 (accept_3_3 32 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 39 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 178 (accept_3_3 29 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 178 (accept_3_3 26 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 39 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 178 (accept_3_3 23 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 178 (accept_3_3 20 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 178
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 178 (accept_3_3 17 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 178 (Polychromatic418967fa.accept_24_16_15_10_1_4733 16 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 178 (accept_3_3 14 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 39 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 178
  (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 178 (accept_3_3 11 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 178 (accept_3_3 8 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 178 (accept_3_3 5 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 39 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 178 (Polychromatic418967fa.accept_15_3_9_13_1_1681 3 39 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 178 (accept_3_3 2 39 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 39 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 178))))))))))))))))))))))))))))))))))))))) (allB_succ 38 178
  (allA_of_3_1 38 38 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 178 (allA_succ_of_accept 36 37 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 178 (accept_3_3 35 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 178 (accept_3_3 32 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 37 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 178 (accept_3_3 29 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 178 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 178 (accept_3_3 26 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 178 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 37 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 178 (accept_3_3 23 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 178 (accept_3_3 20 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 37 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 178
  (Polychromatic418967fa.accept_29_18_8_4_1_10006 18 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 178 (accept_3_3 17 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 178 (accept_3_3 14 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 37 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 178
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 178 (accept_3_3 11 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 178 (Polychromatic418967fa.accept_18_10_1_16_1_579 10 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 178 (accept_3_3 8 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 37 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 178
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 178 (accept_3_3 5 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 37 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 37 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 178 (accept_3_3 2 37 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 37 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 178))))))))))))))))))))))))))))))))))))) (allB_succ 36 178
  (allA_succ_of_accept 35 36 178 (accept_3_3 35 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36
  178 2 17 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  36 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 36 178 2 16 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 36 178 (Polychromatic418967fa.accept_20_11_16_18_1_2885 31 36 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 178 2 15 18 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 178 (accept_3_3 29 36 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 178 2 14 18 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 178
  (Polychromatic418967fa.accept_13_1_10_9_1_215 27 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 178 2 13 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 178 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 36 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 178 2 12 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 178 (accept_3_3 23 36 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 36 178 2 11 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 36 178 (Polychromatic418967fa.accept_19_2_17_7_1_8735 21 36 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 178 2 10 18 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 178 2 9 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 178 (accept_3_3 17 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  178 2 8 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 178 (Polychromatic418967fa.accept_19_15_17_7_1_8734 15 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 178 2 7 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 36 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 178 2 6 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 178 (accept_3_3 11 36 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 178 2 5 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 178 2 4 18 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 178
  (Polychromatic418967fa.accept_15_7_6_13_1_936 7 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 178 2 3 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 178 (accept_3_3 5 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 178
  2 2 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36
  178 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 36 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 36 178 2 1 18 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 36 178 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 36 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 178)))))))))))))))))))))))))))))))))))) (allB_succ 35 178
  (allA_of_3_1 35 35 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 178 (allA_succ_of_accept 33 34 178
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 178 2 16 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 178 (Polychromatic418967fa.accept_14_3_6_10_1_752 31 34 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 178 2 15 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 178 (accept_3_3 29 34 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 178 2 14 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 178 (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 34 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 178 2 13 17 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 178
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 178 2 12 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 178 (accept_3_3 23 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  178 2 11 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 178 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 178 2 10 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 34 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 178 2 9 17 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 178 (accept_3_3 17 34 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 178 2 8 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 178 (Polychromatic418967fa.accept_23_15_11_17_1_10005 15 34
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 178 2 7 17 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 178
  (Polychromatic418967fa.accept_19_13_15_7_1_5843 13 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 178 2 6 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 178 (accept_3_3 11 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  178 2 5 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 178 2 4 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 178 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 34 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 178 2 3 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 178 (accept_3_3 5 34 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 178 2 2 17 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 178 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 34 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 178 2 1 17 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 178
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 34 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 178)))))))))))))))))))))))))))))))))) (allB_succ 33 178 (allA_succ_of_accept 32 33 178 (accept_3_3 32 33
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 178 (Polychromatic418967fa.accept_4_3_1_2_1_62
  31 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 178 (accept_3_3 29 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 178 (accept_3_3 26 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 178
  (Polychromatic418967fa.accept_13_11_7_9_1_612 24 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 178 (accept_3_3 23 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 178 (accept_3_3 20 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 33 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 178
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 178 (accept_3_3 17 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 178 (accept_3_3 14 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 178 (accept_3_3 11 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 178 (accept_3_3 8 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 33 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 178
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 178 (accept_3_3 5 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  178 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 33 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 178 (accept_3_3 2 33 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 178))))))))))))))))))))))))))))))))) (allB_succ 32 178
  (allA_of_3_1 32 32 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 178 (allA_succ_of_accept 30 31 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 178 (accept_3_3 29 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 178 (accept_3_3 26 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 31 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 178 (accept_3_3 23 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 178 (Polychromatic418967fa.accept_19_3_12_7_1_10004 22 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 178 (accept_3_3 20 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 31 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 178
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 178 (accept_3_3 17 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 178 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 178 (accept_3_3 14 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 31 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 178 (accept_3_3 11 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 178 (accept_3_3 8 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 178 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 31 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 178 (accept_3_3 5 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  178 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 31 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 178 (accept_3_3 2 31 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 31 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 178))))))))))))))))))))))))))))))) (allB_succ 30 178
  (allA_succ_of_accept 29 30 178 (accept_3_3 29 30 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  178 2 14 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 178 2 13 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 178 (Polychromatic418967fa.accept_20_5_10_18_1_5622 25 30 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 178 2 12 15 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 178 (accept_3_3 23 30 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 178 2 11 15 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 30 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 178 2 10 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 178 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 30 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 178 2 9 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 178 (accept_3_3 17 30 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 178 2 8 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 178 2 7 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  30 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 178 2 6 15 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 178 (accept_3_3 11
  30 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 178 2 5 15 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 178
  (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 30 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 178 2 4 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 178 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 30 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 178 2 3 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 178 (accept_3_3 5 30 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 178 2 2 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 178 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 30 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 178 2 1 15 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 30
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 178))))))))))))))))))))))))))))))
  (allB_succ 29 178 (allA_of_3_1 29 29 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 178
  (allA_succ_of_accept 27 28 178 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 28 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 178 2 13 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 178 (Polychromatic418967fa.accept_12_1_4_10_1_209
  25 28 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 178 2 12 14 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 178 (accept_3_3 23
  28 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 178 2 11 14 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 28 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 178 2 10 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 19 28 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 178 2 9 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 178 (accept_3_3 17 28 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 178 2 8 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 178 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 28 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 178 2 7 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 178 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  28 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 178 2 6 14 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 178 (accept_3_3 11
  28 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 178 2 5 14 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 178
  (Polychromatic418967fa.accept_16_9_12_2_1_3093 9 28 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 178 2 4 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 28 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 178 2 3 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 178 (accept_3_3 5 28 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 178 2 2 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 28 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 178 2 1 14 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 178 (Polychromatic418967fa.accept_12_1_4_10_1_209 1
  28 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 178))))))))))))))))))))))))))))
  (allB_succ 27 178 (allA_succ_of_accept 26 27 178 (accept_3_3 26 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 27 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 178 (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 27
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 178 (accept_3_3 23 27 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 178 (Polychromatic418967fa.accept_16_6_11_2_1_6485
  22 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 178 (accept_3_3 20 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 178 (accept_3_3 17 27 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 178 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 27 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 178
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 178 (accept_3_3 14 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 178 (Polychromatic418967fa.accept_17_12_10_8_1_5039 12 27 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 178 (accept_3_3 11 27 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 178 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 27
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 178 (accept_3_3 8 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 178 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 27 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 178 (accept_3_3 5 27 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 27 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 178 (Polychromatic418967fa.accept_14_3_13_10_1_761
  3 27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 178 (accept_3_3 2 27
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1
  27 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 178)))))))))))))))))))))))))))
  (allB_succ 26 178 (allA_of_3_1 26 26 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 178
  (allA_succ_of_accept 24 25 178 (Polychromatic418967fa.accept_19_5_6_7_1_10003 24 25 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 178 (accept_3_3 23 25 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 178 (accept_3_3 20 25
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 178 (Polychromatic418967fa.accept_4_3_1_2_1_62
  19 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 178
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 178 (accept_3_3 17 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 178 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 178 (accept_3_3 14 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 25 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 178
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 178 (accept_3_3 11 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 178 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 178 (accept_3_3 8 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 25 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 178
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 178 (accept_3_3 5 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  178 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 25 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 178 (accept_3_3 2 25 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 25 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 178))))))))))))))))))))))))) (allB_succ 24 178
  (allA_succ_of_accept 23 24 178 (accept_3_3 23 24 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24
  178 2 11 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  24 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 24 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 24 178 2 10 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 24 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 24 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 178 2 9 12 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 178 (accept_3_3 17 24 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 24 178 2 8 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 24 178 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 24 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 178 2 7 12 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 178
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 24 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 24 178 2 6 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 24 178 (accept_3_3 11 24 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24
  178 2 5 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  24 178 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 24 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 24 178 2 4 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 24 178 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 24 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 178 2 3 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 178 (accept_3_3 5 24 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 178 2 2 12 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 24 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 24 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 178 2 1 12 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 178
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 24 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 24 178)))))))))))))))))))))))) (allB_succ 23 178 (allA_of_3_1 23 23 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 22 178 (allA_succ_of_accept 21 22 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 22 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 22 178 2 10 11 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 22 178
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 22 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 22 178 2 9 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 22 178 (accept_3_3 17 22 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22
  178 2 8 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  22 178 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 22 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 22 178 2 7 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 22 178 (Polychromatic418967fa.accept_17_13_5_8_1_896 13 22 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 178 2 6 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 178 (accept_3_3 11 22 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 178 2 5 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 22 178 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 22 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 22 178 2 4 11 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 22 178
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 22 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 22 178 2 3 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 22 178 (accept_3_3 5 22 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 178
  2 2 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 22
  178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 22 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 22 178 2 1 11 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 22 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 22 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 22 178)))))))))))))))))))))) (allB_succ 21 178 (allA_succ_of_accept 20 21
  178 (accept_3_3 20 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 21 178 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 21 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 178 (accept_3_3 17 21 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 21 178 (Polychromatic418967fa.accept_13_3_8_9_1_1134 16 21 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 178 (accept_3_3 14 21
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 178 (Polychromatic418967fa.accept_6_1_3_4_1_1
  13 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 178
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 178 (accept_3_3 11 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 178 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 178 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 21 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 178 (accept_3_3 8 21 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 21 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 178
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 178 (accept_3_3 5 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  178 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 21 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 21 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 178 (accept_3_3 2 21 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 21 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 178))))))))))))))))))))) (allB_succ 20 178 (allA_of_3_1 20 20
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 178 (allA_succ_of_accept 18 19 178
  (Polychromatic418967fa.accept_23_18_19_17_1_5029 18 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 19 178 (accept_3_3 17 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 19 178 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 19 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 19 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 178 (accept_3_3 14 19 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  19 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 178
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 178 (accept_3_3 11 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 178 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 19 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 178 (accept_3_3 8 19 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 178 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 19 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 178
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 178 (accept_3_3 5 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  178 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 19 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 178 (accept_3_3 2 19 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 19 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 178))))))))))))))))))) (allB_succ 18 178 (allA_succ_of_accept 17
  18 178 (accept_3_3 17 18 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 178 2 8 9 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 178 2 7 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 178 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 18 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 178 2 6 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 178 (accept_3_3 11 18 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 178 2 5 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 178 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 18 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 178 2 4 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 178 (Polychromatic418967fa.accept_14_7_4_10_1_1351 7
  18 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 178 2 3 9 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 178 (accept_3_3 5 18
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 178 2 2 9 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 178
  (Polychromatic418967fa.accept_12_3_6_10_1_576 3 18 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 178 2 1 9 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 178 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 18 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 178)))))))))))))))))) (allB_succ 17 178 (allA_of_3_1 17 17 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 178 (allA_succ_of_accept 15 16 178
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 16 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 178 2 7 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 16 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 178 2 6 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 178 (accept_3_3 11 16 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 178 2 5 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 178 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 16 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 178 2 4 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 178 (Polychromatic418967fa.accept_12_7_4_10_1_572 7
  16 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 178 2 3 8 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 178 (accept_3_3 5 16
  178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 178 2 2 8 89 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 178
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 16 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 178 2 1 8 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 178 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 16 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 178)))))))))))))))) (allB_succ 15 178 (allA_succ_of_accept 14 15 178
  (accept_3_3 14 15 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 178
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 15 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 178 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 178 (accept_3_3 11 15 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 15 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 178 (accept_3_3 8 15 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 178
  (Polychromatic418967fa.accept_11_6_4_2_1_599 6 15 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 178 (accept_3_3 5 15 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  178 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 15 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 15 178 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 15 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 178 (accept_3_3 2 15 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 15 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 15 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 178))))))))))))))) (allB_succ 14 178 (allA_of_3_1 14 14 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 178 (allA_succ_of_accept 12 13 178
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 13 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 178 (accept_3_3 11 13 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 13 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 178 (accept_3_3 8 13 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 13 178 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 178
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 13 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 178 (accept_3_3 5 13 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  178 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 13 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 13 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 178 (accept_3_3 2 13 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 178 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 13 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 178))))))))))))) (allB_succ 12 178 (allA_succ_of_accept 11 12
  178 (accept_3_3 11 12 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 178 2 5 6 89 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12 178
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 12 178 2 4 6 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 12 178 (Polychromatic418967fa.accept_16_7_12_2_1_8902 7 12 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 178 2 3 6 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 178 (accept_3_3 5 12 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 12 178 2 2 6 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 12 178 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 12 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 178 2 1 6 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 178 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 12
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 178)))))))))))) (allB_succ 11 178
  (allA_of_3_1 11 11 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 10 178 (allA_succ_of_accept 9 10 178
  (Polychromatic418967fa.accept_19_9_10_7_1_10002 9 10 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 10 178 2 4 5 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 10 178 (Polychromatic418967fa.accept_20_7_10_18_1_10001 7 10 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 10 178 2 3 5 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 10 178 (accept_3_3 5 10 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 10 178 2 2 5 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 10 178 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 10 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 10 178 2 1 5 89 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 10 178 (Polychromatic418967fa.accept_11_1_10_2_1_58 1
  10 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 178)))))))))) (allB_succ 9 178
  (allA_succ_of_accept 8 9 178 (accept_3_3 8 9 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 178
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 9 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 178 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 178 (accept_3_3 5 9 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 178 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 9 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 178 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 178 (accept_3_3 2 9 178
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 178 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9
  178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 178))))))))) (allB_succ 8 178
  (allA_of_3_1 8 8 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 178 (allA_succ_of_accept 6 7 178
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 7 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 178 (accept_3_3 5 7 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 178
  (Polychromatic418967fa.accept_12_4_7_10_1_563 4 7 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 178 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 178 (accept_3_3 2 7 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 7 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 178))))))) (allB_succ 6 178 (allA_succ_of_accept 5 6 178
  (accept_3_3 5 6 178 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 178 2 2 3 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 178
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 6 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 178 2 1 3 89 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 178 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 6 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 178)))))) (allB_succ 5 178 (allA_of_3_1 5 5 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 178 (allA_succ_of_accept 3 4 178 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 4 178
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 178 2 1 2 89 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 178
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 4 178 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 178)))) (allB_succ 3 178 (allA_succ_of_accept 2 3 178 (accept_3_3 2 3 178 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 178 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 3 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 178))) (allB_succ 2 178 (allA_of_3_1 2 2 178 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  178))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


