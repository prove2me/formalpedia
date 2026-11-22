-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch168
-- name    : Polychromatic418967fa_Branch168
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:49.019933+00:00
-- url     : https://prove2.me/theorems/f1c71684-3609-4958-96c7-f389d4873247
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch168_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_168 : allB 168 168 :=
  allB_succ' 2 167 168 (Eq.refl Bool.true) (allA_succ_of_accept 1 167 168 (accept_3_4 1 167 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 168)) (allB_succ' 3 166 168 (Eq.refl Bool.true) (allA_succ_of_gcd 2 166 168 2 1 83
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 168
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 166 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 166 168))) (allB_succ' 4 165 168 (Eq.refl Bool.true) (allA_succ_of_gcd 3 165 168 3 1 55 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 165 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 165 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165 168)))) (allB_succ' 5 164 168 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  164 168 4 1 41 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 164 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 164 168 2 1 82 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 164 168 (accept_3_4 1 164 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  168))))) (allB_succ' 6 163 168 (Eq.refl Bool.true) (allA_succ_of_accept 5 163 168 (accept_3_5 5 163 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 163 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 163 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 168 (accept_3_5 2 163 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 163 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 168)))))) (allB_succ' 7 162 168 (Eq.refl Bool.true) (allA_succ_of_gcd 6 162 168 6 1 27 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 168
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 162 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 162 168 2 2 81 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 162 168 3 1 54 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 162 168 2 1 81 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 162 168 (Polychromatic418967fa.accept_17_1_9_15_1_3186 1 162 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 168))))))) (allB_succ' 8 161 168 (Eq.refl Bool.true) (allA_succ_of_gcd 7
  161 168 7 1 23 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  6 161 168 (Polychromatic418967fa.accept_13_6_5_12_1_307 6 161 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 168 (accept_3_4 4 161 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 161 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 161 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 168 (accept_3_4 1 161 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  168)))))))) (allB_succ' 9 160 168 (Eq.refl Bool.true) (allA_succ_of_gcd 8 160 168 8 1 20 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 168
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 160 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 168 2 3 80 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 168 (accept_3_5 5 160 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  168 4 1 40 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 160 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 168 2 1 80 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 160 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 160 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 168))))))))) (allB_succ' 10 159 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 159 168 3 3 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 159 168 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 159 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 168 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 159 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 168 3 2 53 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 168
  (Polychromatic418967fa.accept_15_5_9_3_1_528 5 159 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 168 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 159 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 168 3 1 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 168 (Polychromatic418967fa.accept_13_2_3_12_1_735 2 159 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 168
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 159 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159 168)))))))))) (allB_succ' 11 158 168 (Eq.refl Bool.true) (allA_succ_of_gcd 10 158 168 2 5 79 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 168
  (Polychromatic418967fa.accept_15_9_8_3_1_557 9 158 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 168 2 4 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 168 (accept_3_4 7 158 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  168 2 3 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 168 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 158 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 168 2 2 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 158 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 158 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 168 2 1 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 168 (accept_3_4 1 158 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 168))))))))))) (allB_succ' 12 157 168 (Eq.refl Bool.true) (allA_succ_of_accept 11
  157 168 (accept_3_5 11 157 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 168
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 157 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 157 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 157 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 168 (accept_3_5 8 157 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 157 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 168 (Polychromatic418967fa.accept_22_6_3_14_1_9379
  6 157 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 168 (accept_3_5 5
  157 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 168
  (Polychromatic418967fa.accept_15_4_7_3_1_119 4 157 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 157 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 157 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 168 (accept_3_5 2 157 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 157 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 157 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 168)))))))))))) (allB_succ' 13 156 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 156 168 12 1 13 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 168 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 156 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 168 2 5 78 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 156 168 3 3 52 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 168 4 2 39 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 156 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 168 6 1 26 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 156 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 168 4 1 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 168 3 1 52 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 168 2 1 78 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 156 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 168))))))))))))) (allB_succ' 14 155 168
  (Eq.refl Bool.true) (allA_succ_of_accept 13 155 168 (accept_3_4 13 155 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 155 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 168 (Polychromatic418967fa.accept_22_11_1_14_1_9333 11 155
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 168 (accept_3_4 10 155
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 168
  (Polychromatic418967fa.accept_15_9_5_3_1_554 9 155 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 155 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 168 (accept_3_4 7 155 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 168 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 155 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 5
  155 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 168 (accept_3_4 4 155
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 155 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 155 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 155 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 168 (accept_3_4 1 155 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 155 168)))))))))))))) (allB_succ' 15 154 168 (Eq.refl Bool.true) (allA_succ_of_gcd 14 154 168 14
  1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154
  168 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 154 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 154 168 2 6 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 154 168 (accept_3_5 11 154 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 168 2 5 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 154 168 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 154 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 168 2 4 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 154 168 7 1 22 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 154 168 2 3 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 168 (accept_3_5 5 154 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 168 2 2 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 168 2 1 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 168 (Polychromatic418967fa.accept_13_1_11_12_1_1322
  1 154 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 168))))))))))))))) (allB_succ' 16
  153 168 (Eq.refl Bool.true) (allA_succ_of_gcd 15 153 168 3 5 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 168 (Polychromatic418967fa.accept_18_14_9_6_1_1777 14 153
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 168
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 153 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 168 3 4 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 153 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 168 (Polychromatic418967fa.accept_19_10_1_16_1_7977 10 153
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 168 3 3 51 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 168
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 153 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 168 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 153 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 168 3 2 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 153 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 168
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 153 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 168 3 1 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 168 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 153 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 153 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 168)))))))))))))))) (allB_succ' 17 152 168
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 152 168 8 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 152 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 152 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 168 2 7 76 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 168 (accept_3_4 13 152 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 168 4 3 38 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 152 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 168 2 5 76 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 152 168 (Polychromatic418967fa.accept_18_9_8_6_1_4021 9 152 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 168 8 1 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 168 (accept_3_4 7 152 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 152 168 2 3 76 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 152 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 152 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 168 4 1 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  152 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 168 2 1 76 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 168 (accept_3_4 1
  152 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 168))))))))))))))))) (allB_succ' 18 151 168 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 151 168 (accept_3_5 17 151 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 151 168 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 151 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 168 (Polychromatic418967fa.accept_16_15_7_8_1_8189 15 151
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 168 (accept_3_5 14 151
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 168
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 151 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 151 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 151 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 168 (accept_3_5 11 151 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 151 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 151 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 168 (Polychromatic418967fa.accept_10_9_1_8_1_755 9
  151 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 168 (accept_3_5 8 151
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 168
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 151 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 151 168 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 151 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 168 (accept_3_5 5 151 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 151 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 151 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 3
  151 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 168 (accept_3_5 2 151
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 168 (Polychromatic418967fa.accept_9_1_7_6_1_75
  1 151 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 168)))))))))))))))))) (allB_succ'
  19 150 168 (Eq.refl Bool.true) (allA_succ_of_gcd 18 150 168 6 3 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 168 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 150
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 168 2 8 75 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 168 3 5 50 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 168 2 7 75 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 168
  (Polychromatic418967fa.accept_19_13_17_16_1_6479 13 150 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 150 168 6 2 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 150 168 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 150 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 168 2 5 75 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 168 3 3 50 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 168 2 4 75 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 168
  (Polychromatic418967fa.accept_19_7_17_16_1_6478 7 150 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 168 6 1 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 168 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 150 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 168 2 2 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 168 3 1 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 168 2 1 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 168 (Polychromatic418967fa.accept_19_1_17_16_1_2578 1 150
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 168))))))))))))))))))) (allB_succ' 20
  149 168 (Eq.refl Bool.true) (allA_succ_of_accept 19 149 168 (accept_3_4 19 149 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 149 168 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 149 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 168
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 168 (accept_3_4 16 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 168 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 168 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 149 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 168 (accept_3_4 13 149 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 149 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 168
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 168 (accept_3_4 10 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 168 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 149 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 168 (accept_3_4 7 149 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 168 (Polychromatic418967fa.accept_25_6_24_18_1_9422 6 149 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 168
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 168 (accept_3_4 4 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 149 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 149 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 168 (accept_3_4 1 149 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 168)))))))))))))))))))) (allB_succ' 21 148 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 148 168 4 5 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 148 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 148 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 168 2 9 74 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 168 (accept_3_5 17 148 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 168 4 4 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 168 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 148
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 168 2 7 74 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 168
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 13 148 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 168 4 3 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 148 168 (accept_3_5 11 148 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  148 168 2 5 74 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 148 168 (Polychromatic418967fa.accept_15_9_13_3_1_535 9 148 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 148 168 4 2 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 148 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 148 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 168 2 3 74 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 168 (accept_3_5 5 148 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 168 4 1 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 148 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 148 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 168 2 1 74 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 168
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 148 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 168))))))))))))))))))))) (allB_succ' 22 147 168 (Eq.refl Bool.true) (allA_succ_of_gcd 21 147 168 21 1 7
  8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 147 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 168 3 6 49 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  147 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 147 168 3 5 49 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 147 168 7 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 147 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 147 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 168 3 4 49 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 168 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  147 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 168
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 168 3 3 49 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 168 7 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 147 168 3 2 49 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 168
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 147 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 168 3 1 49 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 168 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 168)))))))))))))))))))))) (allB_succ' 23
  146 168 (Eq.refl Bool.true) (allA_succ_of_gcd 22 146 168 2 11 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 146 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 146 168 2 10 73 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 146 168 (accept_3_4 19
  146 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 146 168 2 9 73 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 146 168
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 146 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 146 168 2 8 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 146 168 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 146 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 168 2 7 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 168 (accept_3_4 13 146 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 168 2 6 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 168 (Polychromatic418967fa.accept_19_11_13_16_1_8002 11 146
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 168 2 5 73 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 168
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 146 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 168 2 4 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 168 (accept_3_4 7 146 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  168 2 3 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 146 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 168 2 2 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 146 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 146 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 168 2 1 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 168 (accept_3_4 1 146 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 168))))))))))))))))))))))) (allB_succ' 24 145 168 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 145 168 (accept_3_5 23 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 145 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 168 (accept_3_5 20 145 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 168 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 145 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 168
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 168 (accept_3_5 17 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 168 (Polychromatic418967fa.accept_16_15_1_8_1_1585 15 145 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 168 (accept_3_5 14 145 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 145 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 168 (accept_3_5 11 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 168 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 168 (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 145 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 168 (accept_3_5 8 145 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 145 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 168
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 168 (accept_3_5 5 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 145 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 145 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 168 (accept_3_5 2 145 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 168 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 145 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 168)))))))))))))))))))))))) (allB_succ' 25 144 168
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 144 168 24 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 144 168 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 144 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 168 2 11 72 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 168 3 7 48 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 168 4 5 36 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 168
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 144 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 168 6 3 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 168 (Polychromatic418967fa.accept_22_17_12_14_1_9421 17 144 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 168 8 2 18 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 168 3 5 48 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 168 2 7 72 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 168
  (Polychromatic418967fa.accept_11_2_1_3_1_683 13 144 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 168 12 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 168 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 144 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 168 2 5 72 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 168 3 3 48 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 168 8 1 18 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 168
  (Polychromatic418967fa.accept_25_7_19_18_1_9420 7 144 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 168 6 1 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 168 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 144 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 168 4 1 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 168 3 1 48 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 168 2 1 72 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 168 (Polychromatic418967fa.accept_23_1_6_7_1_9419 1 144 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 168))))))))))))))))))))))))) (allB_succ' 26
  143 168 (Eq.refl Bool.true) (allA_succ_of_accept 25 143 168 (accept_3_4 25 143 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 143 168 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 143 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 168 (accept_3_4 22 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 143 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 168 (accept_3_4 19 143 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 168 (Polychromatic418967fa.accept_20_18_3_8_1_7903 18 143 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 168
  (Polychromatic418967fa.accept_16_1_15_8_1_2411 17 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 168 (accept_3_4 16 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 143 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 168 (accept_3_4 13 143 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 143 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 168 (accept_3_4 10 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 168 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 168 (Polychromatic418967fa.accept_19_8_10_16_1_9418 8 143 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 168 (accept_3_4 7 143 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 143 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 168 (accept_3_4 4 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 143 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 143 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 168 (accept_3_4 1 143 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 168)))))))))))))))))))))))))) (allB_succ' 27 142 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 142 168 2 13 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 142 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 142 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 142 168 2 12 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 142 168 (accept_3_5 23 142 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 142 168 2 11 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 142 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 21
  142 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 168 2 10 71 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 168
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 142 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 168 2 9 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 168 (accept_3_5 17 142 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 168 2 8 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 142 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 168 2 7 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 142 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 168 2 6 71 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 168 (accept_3_5 11 142 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 168 2 5 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 168
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 9 142 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 168 2 4 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 168 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 142 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 168 2 3 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 168 (accept_3_5 5 142 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 168 2 2 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 142 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 168 2 1 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  142 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 168)))))))))))))))))))))))))))
  (allB_succ' 28 141 168 (Eq.refl Bool.true) (allA_succ_of_gcd 27 141 168 3 9 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 168
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 168 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 141 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 168 3 8 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 168 (Polychromatic418967fa.accept_10_3_1_8_1_132
  23 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 168
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 22 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 141 168 3 7 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 141 168 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 141 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 168 (Polychromatic418967fa.accept_10_9_1_8_1_755
  19 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 168 3 6 47 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 168
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 168 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 141 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 168 3 5 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 168
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 141 168 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 141 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 168 3 4 47 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 168
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 168 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 141 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 168 3 3 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 168 (Polychromatic418967fa.accept_25_8_16_18_1_9417
  8 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 168
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 168 3 2 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 168 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 141 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 168 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 141
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 168 3 1 47 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 168
  (Polychromatic418967fa.accept_25_2_16_18_1_9416 2 141 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 168 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 141 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 168)))))))))))))))))))))))))))) (allB_succ' 29 140 168 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 140 168 28 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 140 168 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 140 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 168 2 13 70 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 168 (accept_3_4 25 140 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 168 4 6 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 168 (Polychromatic418967fa.accept_15_8_5_3_1_1990
  23 140 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 168 2 11 70 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 140 168 7 3 20 24
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 140 168 4 5 35 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 168
  (accept_3_4 19 140 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 168 2 9 70 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 168
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 140 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 140 168 4 4 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 140 168 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 140 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 168 14 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 168 (accept_3_4 13 140 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 168 4 3 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 140 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 168 2 5 70 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 168
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 140 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 168 4 2 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 140 168 7 1 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 140 168 2 3 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 140 168 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 140 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 168 4 1 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 140 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 168 2 1 70 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 168 (accept_3_4 1 140 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 168))))))))))))))))))))))))))))) (allB_succ' 30 139 168
  (Eq.refl Bool.true) (allA_succ_of_accept 29 139 168 (accept_3_5 29 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 139 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 139 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 168 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 139
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 168 (accept_3_5 26 139
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 168
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 139 168 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 139 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 168 (accept_3_5 23 139 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 139 168 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 139 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 168
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 168 (accept_3_5 20 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 168 (Polychromatic418967fa.accept_17_1_3_15_1_2153 18 139 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 168 (accept_3_5 17 139 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 139 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 168
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 168 (accept_3_5 14 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 168 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 139 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 168 (accept_3_5 11 139 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 139 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 168
  (Polychromatic418967fa.accept_18_9_13_6_1_877 9 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 168 (accept_3_5 8 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 168 (Polychromatic418967fa.accept_23_6_1_7_1_9415 6 139 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 168 (accept_3_5 5 139 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 168 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 139 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 168
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 168 (accept_3_5 2 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 139 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 168)))))))))))))))))))))))))))))) (allB_succ' 31 138 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 138 168 6 5 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 168 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 138 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 168 2 14 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 168 3 9 46 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 168 2 13 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 138 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 168 6 4 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 138 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 168 2 11 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 168 3 7 46 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 168 2 10 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 168
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 138 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 168 6 3 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 138 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 168 2 8 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 168 3 5 46 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 168 2 7 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  138 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 168 6 2 23 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 138 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 168 2 5 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 138 168 3 3 46 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 138 168 2 4 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 168 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 138 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 168 6 1 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 138 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 168 2 2 69 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 168 3 1 46 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 168 2 1 69 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 168
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 138 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 168))))))))))))))))))))))))))))))) (allB_succ' 32 137 168 (Eq.refl Bool.true) (allA_succ_of_accept 31
  137 168 (accept_3_4 31 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 137 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 137 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 168 (accept_3_4 28 137 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 137 168 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 137 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 168
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 168 (accept_3_4 25 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 168 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 137 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 168 (accept_3_4 22 137 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 137 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 168
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 168 (accept_3_4 19 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 168 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 137 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 168 (accept_3_4 16 137 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 168 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 137 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 168
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 168 (accept_3_4 13 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 168 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 137 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 168 (accept_3_4 10 137 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 137 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 168
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 168 (accept_3_4 7 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 168 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 137 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 168 (accept_3_4 4 137 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 137 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 168
  (Polychromatic418967fa.accept_19_2_4_16_1_7984 2 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 168 (accept_3_4 1 137 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  168)))))))))))))))))))))))))))))))) (allB_succ' 33 136 168 (Eq.refl Bool.true) (allA_succ_of_gcd 32 136 168 8 4 17 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 168
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 168 2 15 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 168 (accept_3_5 29 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 168 4 7 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 136 168 (Polychromatic418967fa.accept_26_1_6_12_1_5435 27 136 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 168 2 13 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 25
  136 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 168 8 3 17 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 168 (accept_3_5 23
  136 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 168 2 11 68 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 136 168 4 5 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 136 168 (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 136 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 168 2 9 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 168 (accept_3_5 17 136 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 168 8 2 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 168 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 136
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 168 2 7 68 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 168
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 168 4 3 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 136 168 (accept_3_5 11 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  136 168 2 5 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 136 168 (Polychromatic418967fa.accept_23_9_21_7_1_9414 9 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 136 168 8 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 136 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 136 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 168 2 3 68 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 168 (accept_3_5 5 136 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 168 4 1 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 136 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 168 2 1 68 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 168
  (Polychromatic418967fa.accept_19_1_3_16_1_9413 1 136 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136 168))))))))))))))))))))))))))))))))) (allB_succ' 34 135 168 (Eq.refl Bool.true) (allA_succ_of_gcd 33 135
  168 3 11 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  135 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 135 168 (Polychromatic418967fa.accept_16_15_7_8_1_8189 31 135 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 168 3 10 45 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 168
  (Polychromatic418967fa.accept_25_4_10_18_1_9397 29 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 135 168 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 135 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 168 3 9 45 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 168
  (Polychromatic418967fa.accept_18_8_9_6_1_3989 26 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 168 (Polychromatic418967fa.accept_16_9_7_8_1_1588 25 135 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 168 3 8 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  23 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 168
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 168 3 7 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 135 168 (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 135 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 168 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 135
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 168 3 6 45 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 168
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 168 (Polychromatic418967fa.accept_22_16_3_14_1_7791 16 135 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 168 3 5 45 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 168
  (Polychromatic418967fa.accept_13_1_5_12_1_306 14 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 135 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 168 3 4 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 168
  (Polychromatic418967fa.accept_17_11_16_15_1_5467 11 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 168 (Polychromatic418967fa.accept_20_10_15_8_1_4818 10 135 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 168 3 3 45 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 168
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 168 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 135 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 168 3 2 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 168 (Polychromatic418967fa.accept_19_5_2_16_1_8013 5 135 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 168
  (Polychromatic418967fa.accept_13_4_5_12_1_751 4 135 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 168 3 1 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 135 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 168 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 135 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 168))))))))))))))))))))))))))))))))))
  (allB_succ' 35 134 168 (Eq.refl Bool.true) (allA_succ_of_gcd 34 134 168 2 17 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 168
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 33 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 168 2 16 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 168 (accept_3_4 31 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 168 2 15 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 134 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 168 2 14 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 168
  (Polychromatic418967fa.accept_18_9_8_6_1_4021 27 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 168 2 13 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 168 (accept_3_4 25 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 168 2 12 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 134 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 168 2 11 67 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 168
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 168 2 10 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 168 (accept_3_4 19 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 168 2 9 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 168 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 134 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 168 2 8 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 168 (Polychromatic418967fa.accept_13_2_4_12_1_745
  15 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 168 2 7 67 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 168
  (accept_3_4 13 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 168 2 6 67 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 134 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 168 2 5 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 168 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 134 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 168 2 4 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 168 (accept_3_4 7 134 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 168 2 3 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 134 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 168 2 2 67 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  134 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 168 2 1 67 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 168 (accept_3_4 1
  134 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 168))))))))))))))))))))))))))))))))))) (allB_succ' 36
  133 168 (Eq.refl Bool.true) (allA_succ_of_gcd 35 133 168 7 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 133 168 (Polychromatic418967fa.accept_20_14_13_8_1_4847 34 133
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 168
  (Polychromatic418967fa.accept_17_16_14_15_1_1250 33 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 133 168 (accept_3_5 32 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 133 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 133 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 133 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 168 (accept_3_5 29 133 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 133 168 7 4 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 133 168
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 133 168 (accept_3_5 26 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 133 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 133 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 168 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 133
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 168 (accept_3_5 23 133
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 168
  (Polychromatic418967fa.accept_9_4_7_6_1_255 22 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 133 168 7 3 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 133 168 (accept_3_5 20 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 168 (Polychromatic418967fa.accept_20_18_13_8_1_9398 18 133 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 168 (accept_3_5 17 133 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 133
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 168
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 133 168 7 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 133 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 133 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 133 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 168 (accept_3_5 11 133 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 168
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 168 (accept_3_5 8 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133
  168 7 1 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  133 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 133 168 (accept_3_5 5 133 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 133 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 133 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 133 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 168 (accept_3_5 2 133 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  133 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  168)))))))))))))))))))))))))))))))))))) (allB_succ' 37 132 168 (Eq.refl Bool.true) (allA_succ_of_gcd 36 132 168 12 3
  11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 168
  (Polychromatic418967fa.accept_10_5_2_8_1_135 35 132 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 168 2 17 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 132 168 3 11 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 168 4 8 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 132 168 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 132 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 168 6 5 22 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 168
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 132 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 168 4 7 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 132 168 3 9 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 132 168 2 13 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 132 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 168 12 2 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 168
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 132 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 132 168 2 11 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 168 3 7 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 168 4 5 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 132 168 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 132 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 168 6 3 22 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 168
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 132 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 168 4 4 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 132 168 3 5 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 132 168 2 7 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 132 168 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 132 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 168 12 1 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 168
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 11 132 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 168 2 5 66 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 132 168 3 3 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 132 168 4 2 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 168 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 132 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 168 6 1 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 132 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 168 4 1 33 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 168 3 1 44 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 168 2 1 66 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 168
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 1 132 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 168))))))))))))))))))))))))))))))))))))) (allB_succ' 38 131 168 (Eq.refl Bool.true) (allA_succ_of_accept
  37 131 168 (accept_3_4 37 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 168
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 131 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 131 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 168 (accept_3_4 34 131 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 131 168 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 131 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 168
  (Polychromatic418967fa.accept_19_13_17_16_1_6479 32 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 131 168 (accept_3_4 31 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 131 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 131 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 131 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 168 (accept_3_4 28 131 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 168
  (Polychromatic418967fa.accept_16_11_3_8_1_4597 27 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 131 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 131 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 168 (accept_3_4 25 131 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 131 168 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 131 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 168
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 168 (accept_3_4 22 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 131 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 168 (accept_3_4 19 131 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 168 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 131 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 168
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 168 (accept_3_4 16 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 168 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 168 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 131 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 168 (accept_3_4 13 131 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 131 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 168
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 168 (accept_3_4 10 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 168 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 131 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 168 (accept_3_4 7 131 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 168 (Polychromatic418967fa.accept_15_6_11_3_1_1172 6 131 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 168
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 168 (accept_3_4 4 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 131 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 131 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 168 (accept_3_4 1 131 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 168)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 130 168 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 130 168 2 19 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 130 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 130 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 130 168 2 18 65 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 130 168 (accept_3_5 35 130 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 130 168 2 17 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 130 168
  (Polychromatic418967fa.accept_17_16_11_15_1_4353 33 130 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 130 168 2 16 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 130 168 (Polychromatic418967fa.accept_22_9_20_14_1_9412 31 130 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 168 2 15 65 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 168 (accept_3_5 29
  130 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 130 168 2 14 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 130 168
  (Polychromatic418967fa.accept_20_7_10_8_1_9411 27 130 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 130 168 2 13 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 130 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 130 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 130 168 2 12 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 168 (accept_3_5 23 130 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 168 2 11 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 21
  130 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 168 2 10 65 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 168
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 130 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 168 2 9 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 168 (accept_3_5 17 130 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 168 2 8 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 168 (Polychromatic418967fa.accept_18_15_4_6_1_1763 15 130 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 168 2 7 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 168 (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 130 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 168 2 6 65 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 168 (accept_3_5 11
  130 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 168 2 5 65 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 168
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 130 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 168 2 4 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 130 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 168 2 3 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 168 (accept_3_5 5 130 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 168 2 2 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 130 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 168 2 1 65 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 130
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  168))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 129 168 (Eq.refl Bool.true) (allA_succ_of_gcd 39 129 168 3
  13 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129
  168 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 168 3 12 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 168 3 11 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 129 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 168 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 168 3 10 43 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 168 3 9 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 129 168 3 8 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 129 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 129 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 168 3 7 43 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 168 3 6 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 168 3 5 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 129 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 168 3 4 43 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 168 3 3 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 129 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 168 3 2 43 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 129 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 168 3 1 43 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 129 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 129 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 168)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 128 168
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 128 168 8 5 16 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 128 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 128 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 128 168 2 19 64 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 128 168 (accept_3_4 37 128 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 128 168 4 9 32 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 168
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 128 168 2 17 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 128 168 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 128 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 168 8 4 16 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 168 (accept_3_4 31 128 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 168 2 15 64 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 168
  (Polychromatic418967fa.accept_22_7_18_14_1_7813 29 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 128 168 4 7 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 128 168 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 128 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 168 2 13 64 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 168 (accept_3_4 25
  128 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 168 8 3 16 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 168
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 128 168 2 11 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 128 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 128 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 168 4 5 32 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 168 (accept_3_4 19 128 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 168 2 9 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 168 8 2 16 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 168
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 128 168 2 7 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 128 168 (accept_3_4 13 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  128 168 4 3 32 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 128 168 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 168 2 5 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 168 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 128 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 168 8 1 16 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 168 (accept_3_4 7 128 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 168 2 3 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 128 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 168 4 1 32 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 168 2 1 64 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 168 (accept_3_4 1 128 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  168))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 127 168 (Eq.refl Bool.true) (allA_succ_of_accept 41 127
  168 (accept_3_5 41 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 168
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 127 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 127 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 168 (accept_3_5 38 127 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 127 168 (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 168
  (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 168 (accept_3_5 35 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 168 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 168 (accept_3_5 32 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 127 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 168 (accept_3_5 29 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 168 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 168 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 168 (accept_3_5 26 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 127 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 168
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 127 168 (accept_3_5 23 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 127 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 127 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 127 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 168 (accept_3_5 20 127 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184
  19 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 168
  (Polychromatic418967fa.accept_19_18_13_16_1_9366 18 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 127 168 (accept_3_5 17 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 127 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 127 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 168 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 127
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 168 (accept_3_5 14 127
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 168
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 127 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 127 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 168 (accept_3_5 11 127 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 127 168 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 168
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 168 (accept_3_5 8 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 168 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 168 (accept_3_5 5 127 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 127 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 168 (accept_3_5 2 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 168 (Polychromatic418967fa.accept_16_1_15_8_1_2411 1 127 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 168)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 126 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 126 168 42 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 168 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 126 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 168 2 20 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 168 3 13 42 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 168 2 19 63 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 168
  (Polychromatic418967fa.accept_23_14_11_7_1_9410 37 126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 168 6 6 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 126 168 7 5 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 126 168 2 17 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 168 3 11 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 168 2 16 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 168
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 168 6 5 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 126 168 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 126 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 168 14 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 168 3 9 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 168 2 13 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 168
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 168 6 4 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 168 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 126 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 168 2 11 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 168 21 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 168 2 10 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 168
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 168 6 3 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 168 (Polychromatic418967fa.accept_23_17_11_7_1_9409 17 126 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 168 2 8 63 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 168 3 5 42 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 168 14 1 9 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 168
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 168 6 2 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 126 168 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 126 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 168 2 5 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 168 3 3 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 168 2 4 63 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 126 168 7 1 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 126 168 6 1 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 168 (Polychromatic418967fa.accept_15_5_6_3_1_525 5
  126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 168 2 2 63 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 168 3 1 42 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 168 2 1 63 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 168
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 126 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 168))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 125 168 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 125 168 (accept_3_4 43 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 168 (accept_3_4 40 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 168 (accept_3_4 37 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 168 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 168 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 168 (accept_3_4 34 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 125
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 168 (accept_3_4 31 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 168 (accept_3_4 28 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 168 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 168
  (Polychromatic418967fa.accept_17_9_6_15_1_5454 26 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 168 (accept_3_4 25 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 168 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 168 (accept_3_4 22 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 168 (accept_3_4 19 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 168 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 168 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 168 (accept_3_4 16 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 168 (Polychromatic418967fa.accept_18_15_17_6_1_4043 15 125
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 168 (accept_3_4 13 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 168 (accept_3_4 10 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 168 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 168
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 168 (accept_3_4 7 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 168 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 168 (accept_3_4 4 125 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 125 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 168 (accept_3_4 1 125 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  168)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 124 168 (Eq.refl Bool.true) (allA_succ_of_gcd 44 124
  168 4 11 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  124 168 (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 124 168 2 21 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 124 168 (accept_3_5 41 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 168 4 10 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 124 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 168 2 19 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 168
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 168 4 9 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 168 (accept_3_5 35 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 168 2 17 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 168 (Polychromatic418967fa.accept_16_1_12_8_1_2405 33 124 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 168 4 8 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 31
  124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 168 2 15 62 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 168 (accept_3_5 29
  124 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 168 4 7 31 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 168
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 124 168 2 13 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 124 168 (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 124 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 168 4 6 31 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 168 (accept_3_5 23 124 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 168 2 11 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 168
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 168 4 5 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 124 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 168 2 9 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 168 (accept_3_5 17 124 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 168 4 4 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 168 (Polychromatic418967fa.accept_16_15_12_8_1_4585 15 124
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 168 2 7 62 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 168
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 168 4 3 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 168 (accept_3_5 11 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 168 2 5 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 124 168 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 124 168 4 2 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 124 168 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 124 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 168 2 3 62 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 168 (accept_3_5 5 124 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 168 4 1 31 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 124 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 124 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 168 2 1 62 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 168
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 124 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 168))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 123 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 123 168 3 15 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 168 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 168
  (Polychromatic418967fa.accept_22_21_13_14_1_9408 43 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 123 168 3 14 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 123 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 168
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 40 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 168 3 13 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 168 (Polychromatic418967fa.accept_20_18_3_8_1_7903 38 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 168
  (Polychromatic418967fa.accept_16_5_11_8_1_3431 37 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 123 168 3 12 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 123 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 168
  (Polychromatic418967fa.accept_11_1_2_3_1_688 34 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 168 3 11 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 168 (Polychromatic418967fa.accept_23_9_8_7_1_9407 32 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 168
  (Polychromatic418967fa.accept_10_1_3_8_1_136 31 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 168 3 10 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 168 (Polychromatic418967fa.accept_16_13_11_8_1_2449 29 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 168
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 123 168 3 9 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 123 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 123 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 123
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 168 3 8 41 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 168
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 168 (Polychromatic418967fa.accept_18_4_15_6_1_3994 22 123 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 168 3 7 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 168 (Polychromatic418967fa.accept_13_7_6_12_1_2027
  20 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 168
  (Polychromatic418967fa.accept_16_3_11_8_1_830 19 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 123 168 3 6 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 123 168 (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 123 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  16 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 168 3 5 41 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 168
  (Polychromatic418967fa.accept_19_14_9_16_1_7969 14 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 123 168 (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 123 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 168 3 4 41 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 168
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 168 (Polychromatic418967fa.accept_13_10_6_12_1_2780 10 123 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 168 3 3 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 168 (Polychromatic418967fa.accept_19_8_9_16_1_9406
  8 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 168
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 168 3 2 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 123 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 168 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 123
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 168 3 1 41 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 168
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 123 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 123 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 168)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 122 168
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 122 168 2 23 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 122 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 122 168 2 22 61 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 122 168 (accept_3_4 43
  122 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 122 168 2 21 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 122 168
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 122 168 2 20 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 122 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 122 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 122 168 2 19 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 122 168 (accept_3_4 37 122 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 122 168 2 18 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 122 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 35
  122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 168 2 17 61 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 168
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 168 2 16 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 168 (accept_3_4 31 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 168 2 15 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 122 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 168 2 14 61 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 168
  (Polychromatic418967fa.accept_13_1_5_12_1_306 27 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 168 2 13 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 168 (accept_3_4 25 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 168 2 12 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 168 (Polychromatic418967fa.accept_27_23_14_6_1_9405 23 122 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 168 2 11 61 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 168
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 168 2 10 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 168 (accept_3_4 19 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 168 2 9 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 122 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 168 2 8 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 168 (Polychromatic418967fa.accept_10_5_2_8_1_135
  15 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 168 2 7 61 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 168
  (accept_3_4 13 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 168 2 6 61 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 168
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 168 2 5 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 168 (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 122 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 168 2 4 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 168 (accept_3_4 7 122 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 168 2 3 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 122 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 168 2 2 61 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 3
  122 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 168 2 1 61 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 168 (accept_3_4 1
  122 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 168)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 121 168 (Eq.refl Bool.true) (allA_succ_of_accept 47 121 168 (accept_3_5 47 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 168
  (Polychromatic418967fa.accept_18_9_13_6_1_877 45 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 168 (accept_3_5 44 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 168 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 168 (accept_3_5 41 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 168 (Polychromatic418967fa.accept_19_2_7_16_1_9312 40 121
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 168
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 168 (accept_3_5 38 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 168 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 168 (accept_3_5 35 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 121 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 168
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 168 (accept_3_5 32 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 168 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 168 (accept_3_5 29 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 168
  (Polychromatic418967fa.accept_17_10_2_15_1_3179 27 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 121 168 (accept_3_5 26 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 121 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 121 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 168 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 121
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 168 (accept_3_5 23 121
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 168
  (Polychromatic418967fa.accept_23_22_6_7_1_9404 22 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 121 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 168 (accept_3_5 20 121 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 121 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 168
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 168 (accept_3_5 17 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 168 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 168 (accept_3_5 14 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 168 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 121
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 168
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 168 (accept_3_5 11 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 168 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 168 (accept_3_5 8 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 168
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 168 (accept_3_5 5 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 168 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 121 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 168 (accept_3_5 2 121 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 121 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 168))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 120 168 (Eq.refl Bool.true) (allA_succ_of_gcd 48 120 168 24 2 5 7 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 120 168 2 23 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 120 168 3 15 40 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 168 4 11 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 168 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 120 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 168 6 7 20 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 168
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 168 8 5 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 120 168 3 13 40 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 120 168 2 19 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 120 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 120 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 168 12 3 10 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 168
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 168 2 17 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 120 168 3 11 40 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 168 8 4 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 120 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 120 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 168 6 5 20 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 168 4 7 30 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 120 168 3 9 40 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 120 168 2 13 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 120 168 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 120 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 168 24 1 5 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 168 2 11 60 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 168 3 7 40 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 168 4 5 30 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 168
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 168 6 3 20 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 120 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 168 8 2 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 168 3 5 40 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 168 2 7 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 13
  120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 168 12 1 10 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 168 2 5 60 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 120 168 3 3 40 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 120 168 8 1 15 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 168 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 168 6 1 20 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 120 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 168 4 1 30 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 168 3 1 40 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 168 2 1 60 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 168
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 168))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 119 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 119 168 7 7 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 119 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 168 (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 119
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 168 (accept_3_4 46 119
  168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 168
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 119 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 168 (accept_3_4 43 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 119 168 7 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 119 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 119 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 168 (accept_3_4 40 119 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 168
  (Polychromatic418967fa.accept_29_9_3_23_1_9403 38 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 168 (accept_3_4 37 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 168 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 119 168 7 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 119 168 (accept_3_4 34 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 119 168 (Polychromatic418967fa.accept_16_1_7_8_1_3422 33 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 168 (accept_3_4 31 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 168 (Polychromatic418967fa.accept_9_3_2_6_1_264
  30 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 168
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 119 168 7 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 119 168 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 168 (accept_3_4 25 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 168 (Polychromatic418967fa.accept_10_4_9_8_1_125
  24 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 168
  (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 168 (accept_3_4 22 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21
  119 168 7 3 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  20 119 168 (Polychromatic418967fa.accept_16_4_7_8_1_5753 20 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 119 168 (accept_3_4 19 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 119 168 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 168 (accept_3_4 16 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 168
  (Polychromatic418967fa.accept_16_15_7_8_1_8189 15 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 119 168 7 2 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 119 168 (accept_3_4 13 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 168 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 119 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 168 (accept_3_4 10 119 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 168 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 168
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 119 168 7 1 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 119 168 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 119 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 168 (accept_3_4 4 119 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 168 (Polychromatic418967fa.accept_9_3_2_6_1_264 3
  119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 168
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 168 (accept_3_4 1 119 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  168)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 118 168 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  118 168 2 25 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 118 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 118 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 118 168 2 24 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 118 168 (accept_3_5 47 118 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 118 168 2 23 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 118 168 (Polychromatic418967fa.accept_17_11_16_15_1_5467 45 118
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 168 2 22 59 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 168
  (Polychromatic418967fa.accept_9_7_1_6_1_261 43 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 168 2 21 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 168 (accept_3_5 41 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 168 2 20 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 118 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 168 2 19 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 168
  (Polychromatic418967fa.accept_13_11_1_12_1_742 37 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 168 2 18 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 168 (accept_3_5 35 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 168 2 17 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 168 (Polychromatic418967fa.accept_18_15_10_6_1_1781 33 118 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 168 2 16 59 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 168
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 168 2 15 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 168 (accept_3_5 29 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 168 2 14 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 168 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 118 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 168 2 13 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 168
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 168 2 12 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 168 (accept_3_5 23 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 168 2 11 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 118 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 168 2 10 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 168
  (Polychromatic418967fa.accept_23_19_3_7_1_9402 19 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 168 2 9 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 168 (accept_3_5 17 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 168 2 8 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 168 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 168 2 7 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 118 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 168 2 6 59 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 168 (accept_3_5 11 118 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 168 2 5 59 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 168
  (Polychromatic418967fa.accept_15_9_13_3_1_535 9 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 168 2 4 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 118 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 168 2 3 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 168 (accept_3_5 5 118 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 168 2 2 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 118 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 168 2 1 59 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 168 (Polychromatic418967fa.accept_15_1_13_3_1_2002
  1 118 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  168))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 117 168 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  117 168 3 17 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 117 168 (Polychromatic418967fa.accept_18_14_9_6_1_1777 50 117 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 117
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 168 3 16 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 168
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 168 (Polychromatic418967fa.accept_27_19_9_6_1_9373 46 117 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 117 168 3 15 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 117 168 (Polychromatic418967fa.accept_16_12_5_8_1_2492
  44 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 168
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 117 168 3 14 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 117 168 (Polychromatic418967fa.accept_22_19_7_14_1_9343 41 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 168
  (Polychromatic418967fa.accept_19_2_3_16_1_6469 40 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 117 168 3 13 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 117 168 (Polychromatic418967fa.accept_15_8_12_3_1_1912 38 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 168
  (Polychromatic418967fa.accept_11_4_7_3_1_289 37 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 168 3 12 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 168 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 168
  (Polychromatic418967fa.accept_19_15_3_16_1_9382 34 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 117 168 3 11 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 117 168 (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 168
  (Polychromatic418967fa.accept_18_13_9_6_1_4024 31 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 117 168 3 10 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 117 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 168
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 117 168 3 9 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 117 168 (Polychromatic418967fa.accept_11_4_7_3_1_289 26 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 168
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 168 3 8 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 168 (Polychromatic418967fa.accept_15_8_12_3_1_1912 23 117 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 168 (Polychromatic418967fa.accept_15_7_12_3_1_1137 22 117
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 168 3 7 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 168
  (Polychromatic418967fa.accept_16_4_5_8_1_2425 20 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 117 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 168 3 6 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 168 (Polychromatic418967fa.accept_15_2_12_3_1_1183
  17 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 168
  (Polychromatic418967fa.accept_22_16_7_14_1_9401 16 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 117 168 3 5 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 117 168 (Polychromatic418967fa.accept_18_14_9_6_1_1777 14 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 168
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 117 168 3 4 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 117 168 (Polychromatic418967fa.accept_16_11_5_8_1_2427 11 117 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 168
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 10 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 168 3 3 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 168 (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 117 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 168 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 117
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 168 3 2 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 168
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 168 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 117 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 168 3 1 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 168 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 117 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 168
  (Polychromatic418967fa.accept_18_1_9_6_1_6630 1 117 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 168)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 116 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 52 116 168 4 13 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 116 168 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 116 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 116 168 2 25 58 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 116 168 (accept_3_4 49 116 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 116 168 4 12 29 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 116 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 116 168 2 23 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 116 168 (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 116 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 116 168 4 11 29 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 116 168 (accept_3_4 43 116 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 116 168 2 21 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 116 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 116 168 4 10 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 116 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 116 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 116 168 2 19 58 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 116 168 (accept_3_4 37 116 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 116 168 4 9 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 116 168 (Polychromatic418967fa.accept_16_3_4_8_1_3450
  35 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 168 2 17 58 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 168
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 168 4 8 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 116 168 (accept_3_4 31 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  116 168 2 15 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 116 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 116 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 168 4 7 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 168 (Polychromatic418967fa.accept_16_11_4_8_1_3435
  27 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 168 2 13 58 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 168
  (accept_3_4 25 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 168 4 6 29 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 116 168 2 11 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 116 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 116 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 168 4 5 29 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 168 (accept_3_4 19 116 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 168 2 9 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 168 (Polychromatic418967fa.accept_16_1_4_8_1_3434
  17 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 168 4 4 29 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 168
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 168 2 7 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 116 168 (accept_3_4 13 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  116 168 4 3 29 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 116 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 168 2 5 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 168 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 116 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 168 4 2 29 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 168 (accept_3_4 7 116 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 168 2 3 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 116 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 168 4 1 29 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 168
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 168 2 1 58 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 168 (accept_3_4 1 116 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  168))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 115 168 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 115 168 (accept_3_5 53 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 168 (Polychromatic418967fa.accept_15_6_10_3_1_2844 51 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 168 (accept_3_5 50 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 115 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 168
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 168 (accept_3_5 47 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 168 (Polychromatic418967fa.accept_16_13_3_8_1_2422 45 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 168 (accept_3_5 44 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 115
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 168
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 168 (accept_3_5 41 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 115 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 168 (accept_3_5 38 115 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 168
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 115 168 (accept_3_5 35 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 115 168 (Polychromatic418967fa.accept_19_15_1_16_1_6499 34 115 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  33 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 168 (accept_3_5 32
  115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 168
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 115 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 115 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 168 (accept_3_5 29 115 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 115 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 115 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 168 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  27 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 168 (accept_3_5 26
  115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 168
  (Polychromatic418967fa.accept_17_8_13_15_1_2143 25 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 168 (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 168 (accept_3_5 23 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 115 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 168
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 168 (accept_3_5 20 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 168 (Polychromatic418967fa.accept_27_18_7_6_1_9400 18 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 168 (accept_3_5 17 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 168 (Polychromatic418967fa.accept_22_16_5_14_1_9301 16 115
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 168
  (Polychromatic418967fa.accept_19_15_1_16_1_6499 15 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 115 168 (accept_3_5 14 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 115 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 115 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 115 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 168 (accept_3_5 11 115 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 10
  115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 168
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 9 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 168 (accept_3_5 8 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 168 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 168 (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 168 (accept_3_5 5 115 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 115 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 168
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 168 (accept_3_5 2 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 115 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 168)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 114 168 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 114 168 6 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 114 168 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 114 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 168 2 26 57 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 168 3 17 38 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 168 2 25 57 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 168
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 168 6 8 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 168 (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 114 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 168 2 23 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 168 3 15 38 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 168 2 22 57 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 168
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 168 6 7 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 168 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 114 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 168 2 20 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 168 3 13 38 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 168 2 19 57 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 168
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 37 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 114 168 6 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 168 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 114 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 168 2 17 57 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 168 3 11 38 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 168 2 16 57
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 168
  (Polychromatic418967fa.accept_17_14_12_15_1_5558 31 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 114 168 6 5 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 114 168 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 114 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 168 2 14 57 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 168 3 9 38 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 168 2 13 57 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 168
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 168 6 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 168 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 114 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 168 2 11 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 168 3 7 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 168 2 10 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 168
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 168 6 3 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 168 (Polychromatic418967fa.accept_29_17_27_23_1_9399 17 114 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 168 2 8 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 168 3 5 38 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 168 2 7 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 168
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 168 6 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 168 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 114 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 168 2 5 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 168 3 3 38 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 168 2 4 57 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 168
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 114 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 168 6 1 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 168 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 114 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 168 2 2 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 168 3 1 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 168 2 1 57 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 168 (Polychromatic418967fa.accept_17_1_12_15_1_1263 1 114
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  168))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 113 168 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 113 168 (accept_3_4 55 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 168 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 168 (accept_3_4 52 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 168
  (Polychromatic418967fa.accept_15_5_8_3_1_556 50 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 168 (accept_3_4 49 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 168 (accept_3_4 46 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 168
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 168 (accept_3_4 43 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 168 (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 168 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 168 (accept_3_4 40 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 168
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 168 (accept_3_4 37 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 168 (accept_3_4 34 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 168 (Polychromatic418967fa.accept_17_16_11_15_1_4353 33 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 168
  (Polychromatic418967fa.accept_19_13_18_16_1_5123 32 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 113 168 (accept_3_4 31 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 113 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 168 (accept_3_4 28 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 168
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 113 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 168 (accept_3_4 25 113 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 168 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 168
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 113 168 (accept_3_4 22 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 113 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 168 (accept_3_4 19 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 168
  (Polychromatic418967fa.accept_20_18_13_8_1_9398 18 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 168 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 168 (accept_3_4 16 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 168
  (Polychromatic418967fa.accept_19_14_18_16_1_6530 14 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 168 (accept_3_4 13 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 113 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 168 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 168 (accept_3_4 10 113 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 168 (Polychromatic418967fa.accept_15_9_8_3_1_557 9
  113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 168
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 168 (accept_3_4 7 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 168 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 168 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 168 (accept_3_4 4 113 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 168 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 113 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 168
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 168 (accept_3_4 1 113 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  168)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 112 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 112 168 56 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 112 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 112 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 112 168 2 27 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 112 168 (accept_3_5 53 112 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 112 168 4 13 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 112 168 (Polychromatic418967fa.accept_18_15_4_6_1_1763 51 112
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 168 2 25 56 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 112 168 7 7 16 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 112 168 8 6 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 112 168 (accept_3_5 47
  112 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 112 168 2 23 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 112 168
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 112 168 4 11 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 112 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 112 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 168 14 3 8 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 168 (accept_3_5 41 112 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 168 8 5 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 39
  112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 168 2 19 56 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 168
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 168 4 9 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 112 168 7 5 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 112 168 2 17 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 168 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 112 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 168 8 4 14 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 168
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 168 2 15 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 168 (accept_3_5 29 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 168 28 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 112 168 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 112 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 168 2 13 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 168 (Polychromatic418967fa.accept_9_7_4_6_1_273 25
  112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 168 8 3 14 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 168 (accept_3_5 23
  112 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 168 2 11 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 112 168 7 3 16 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 112 168 4 5 28 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 168
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 168 2 9 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 168 (accept_3_5 17 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 168 8 2 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 168 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 168 14 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 168 (Polychromatic418967fa.accept_19_13_17_16_1_6479 13 112 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 168 4 3 28 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 168 (accept_3_5 11
  112 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 168 2 5 56 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 168
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 168 8 1 14 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 112 168 7 1 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 112 168 2 3 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 168 (accept_3_5 5 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  168 4 1 28 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 168 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 168 2 1 56 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 168 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 112 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 168)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 111 168 (Eq.refl Bool.true) (allA_succ_of_gcd 57 111 168 3 19 37 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 168 3 18 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 52 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 111 168 3 17 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 111 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 111 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 168 (Polychromatic418967fa.accept_9_4_3_6_1_532
  49 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 168 3 16 37 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 168 3 15 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 44
  111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 168 3 14 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 111 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 168 (Polychromatic418967fa.accept_9_4_3_6_1_532
  40 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 168 3 13 37 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 168 3 12 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 168 3 11 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 111 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 168 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 168 3 10 37 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 168 3 9 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 168 3 8 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 111 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 168 3 7 37 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 168 3 6 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 168 3 5 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 168 3 4 37 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 168 3 3 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 168 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 168
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 168 3 2 37 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 168 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 168 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 111 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 168 3 1 37 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 168
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 111 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 168 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 111 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111 168))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 110 168 (Eq.refl Bool.true) (allA_succ_of_gcd 58 110 168 2 29 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 57 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 168 2 28 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 168 (accept_3_4 55 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 168 2 27 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 110 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 168 2 26 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 168
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 51 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 168 2 25 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 168 (accept_3_4 49 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 168 2 24 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 168 (Polychromatic418967fa.accept_15_2_5_3_1_552 47 110 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 168 2 23 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 168
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 45 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 168 2 22 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 168 (accept_3_4 43 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 168 2 21 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 110 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 168 2 20 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 168 2 19 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 168 (accept_3_4 37 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 168 2 18 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 110 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 168 2 17 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 168
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 168 2 16 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 168 (accept_3_4 31 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 168 2 15 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 168 (Polychromatic418967fa.accept_25_4_10_18_1_9397 29 110 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 168 2 14 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 168
  (Polychromatic418967fa.accept_17_10_8_15_1_8104 27 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 110 168 2 13 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 110 168 (accept_3_4 25 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 168 2 12 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 110 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 168 2 11 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 168 2 10 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 168 (accept_3_4 19 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 168 2 9 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 168 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 110 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 168 2 8 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 168 (Polychromatic418967fa.accept_13_2_6_12_1_1334
  15 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 168 2 7 55 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 168
  (accept_3_4 13 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 168 2 6 55 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 168
  (Polychromatic418967fa.accept_19_11_15_16_1_9396 11 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 110 168 2 5 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 110 168 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 110 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 168 2 4 55 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 168 (accept_3_4 7 110 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 168 2 3 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 110 168 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 110 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 168 2 2 55 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 168
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 110 168 2 1 55 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 110 168 (accept_3_4 1 110 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  168))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 109 168 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 109 168 (accept_3_5 59 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 168 (accept_3_5 56 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 168 (Polychromatic418967fa.accept_19_17_14_16_1_3820 55 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 168
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 168 (accept_3_5 53 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 168 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 168 (accept_3_5 50 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 168 (accept_3_5 47 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 168 (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 168 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 168 (accept_3_5 44 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 168
  (Polychromatic418967fa.accept_27_15_1_6_1_9395 42 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 168 (accept_3_5 41 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 168 (accept_3_5 38 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 168 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 168
  (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 168 (accept_3_5 35 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 168 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 168 (accept_3_5 32 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 168 (accept_3_5 29 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 168 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 168 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 168 (accept_3_5 26 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 168
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 168 (accept_3_5 23 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 168 (accept_3_5 20 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 168 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 168
  (Polychromatic418967fa.accept_11_7_10_3_1_633 18 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 168 (accept_3_5 17 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 168 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 168 (accept_3_5 14 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 168
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 168 (accept_3_5 11 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 168 (Polychromatic418967fa.accept_22_10_21_14_1_9394 10 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 168 (Polychromatic418967fa.accept_17_9_7_15_1_4346 9 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 168 (accept_3_5 8 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 168 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 168
  (Polychromatic418967fa.accept_13_6_5_12_1_307 6 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 168 (accept_3_5 5 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 168 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 109 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 168 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 168 (accept_3_5 2 109 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 168 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 109 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  168)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 108 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 108 168 12 5 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 108 168 (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 108 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 168 2 29 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 168 3 19 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 168 4 14 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 168
  (Polychromatic418967fa.accept_13_3_4_12_1_36 55 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 168 6 9 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 168 (Polychromatic418967fa.accept_16_5_12_8_1_2521 53 108 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 168 4 13 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 168 3 17 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 168 2 25 54 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 168
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 49 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 168 12 4 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 168 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 108 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 168 2 23 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 168 3 15 36 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 168 4 11 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 168
  (Polychromatic418967fa.accept_16_11_12_8_1_1592 43 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 108 168 6 7 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 108 168 (Polychromatic418967fa.accept_13_2_4_12_1_745 41 108 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 168 4 10 27 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 168 3 13 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 168 2 19 54 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 168
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 37 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 168 12 3 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 168 (Polychromatic418967fa.accept_16_3_12_8_1_808 35 108 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 168 2 17 54 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 168 3 11 36 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 168 4 8 27 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 168
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 168 6 5 18 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 168 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 108 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 168 4 7 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 168 3 9 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 168 2 13 54 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 168
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 25 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 168 12 2 9 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 168 (Polychromatic418967fa.accept_16_7_12_8_1_2450 23 108 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 168 2 11 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 168 3 7 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 168 4 5 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 168 (Polychromatic418967fa.accept_16_3_12_8_1_808
  19 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 168 6 3 18 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 168
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 168 4 4 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 108 168 3 5 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 108 168 2 7 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 108 168 (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 108 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 168 12 1 9 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 168
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 168 2 5 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 168 3 3 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 168 4 2 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 108 168 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 108 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 168 6 1 18 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 168
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 108 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 168 4 1 27 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 168 3 1 36 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 168 2 1 54 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 168 (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 108 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108 168)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 107 168 (Eq.refl Bool.true) (allA_succ_of_accept 61 107 168 (accept_3_4 61 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 168 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 168 (accept_3_4 58 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 56 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 168 (accept_3_4 55 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 168 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 168
  (Polychromatic418967fa.accept_16_5_11_8_1_3431 53 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 168 (accept_3_4 52 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 168 (Polychromatic418967fa.accept_16_3_11_8_1_830 51 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 50 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 168 (accept_3_4 49 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 168 (accept_3_4 46 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 168 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 168 (Polychromatic418967fa.accept_15_14_2_3_1_1980 44 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 168 (accept_3_4 43 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 168 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 107
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 41 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 168 (accept_3_4 40 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 38 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 168 (accept_3_4 37 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 168 (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 107 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 168
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 168 (accept_3_4 34 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 168 (Polychromatic418967fa.accept_18_15_17_6_1_4043 33 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 32 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 168 (accept_3_4 31 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 168 (accept_3_4 28 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 168 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 168 (Polychromatic418967fa.accept_19_7_12_16_1_9393 26 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 168 (accept_3_4 25 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 168 (Polychromatic418967fa.accept_17_7_5_15_1_3184 24 107
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 168 (accept_3_4 22 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 168 (accept_3_4 19 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 168 (Polychromatic418967fa.accept_29_18_20_23_1_9392 18 107 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 168
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 168 (accept_3_4 16 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 168 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 168 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 168 (accept_3_4 13 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 168
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 168 (accept_3_4 10 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 168 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 168 (Polychromatic418967fa.accept_23_8_15_7_1_7758 8 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 168 (accept_3_4 7 107 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 168 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 107 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 168
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 168 (accept_3_4 4 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 168 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 107 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 168 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 168 (accept_3_4 1 107 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 168)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  106 168 (Eq.refl Bool.true) (allA_succ_of_gcd 62 106 168 2 31 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 168 (Polychromatic418967fa.accept_17_10_4_15_1_2165 61 106
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 106 168 2 30 53 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 106 168 (accept_3_5 59
  106 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 106 168 2 29 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 106 168
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 106 168 2 28 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 106 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 106 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 106 168 2 27 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 106 168 (accept_3_5 53 106 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 106 168 2 26 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 106 168 (Polychromatic418967fa.accept_15_6_1_3_1_2852
  51 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 168 2 25 53 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 168
  (Polychromatic418967fa.accept_9_4_7_6_1_255 49 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 168 2 24 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 168 (accept_3_5 47 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 168 2 23 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 168 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 106 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 168 2 22 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 168
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 168 2 21 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 168 (accept_3_5 41 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 168 2 20 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 106 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 168 2 19 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 168
  (Polychromatic418967fa.accept_9_1_7_6_1_75 37 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 168 2 18 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 168 (accept_3_5 35 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 168 2 17 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 168 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 106 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 168 2 16 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 168
  (Polychromatic418967fa.accept_9_4_7_6_1_255 31 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 168 2 15 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 168 (accept_3_5 29 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 168 2 14 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 168 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 106 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 168 2 13 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 168
  (Polychromatic418967fa.accept_19_6_11_16_1_9391 25 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 106 168 2 12 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 106 168 (accept_3_5 23 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 168 2 11 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 106 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 168 2 10 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 168
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 168 2 9 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 168 (accept_3_5 17 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 168 2 8 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 168 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 168 2 7 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 168 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 106 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 168 2 6 53 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 168 (accept_3_5 11 106 168
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 168 2 5 53 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 168
  (Polychromatic418967fa.accept_25_9_6_18_1_9390 9 106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 168 2 4 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 168 (Polychromatic418967fa.accept_22_7_18_14_1_7813 7 106 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 168 2 3 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 168 (accept_3_5 5 106 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 168 2 2 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 168 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 106 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 168 2 1 53 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 168 (Polychromatic418967fa.accept_9_1_7_6_1_75 1
  106 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  168))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 105 168 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 105 168 21 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 105 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 168 (Polychromatic418967fa.accept_19_4_10_16_1_6531 61 105
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 168 3 20 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 168
  (Polychromatic418967fa.accept_18_5_15_6_1_3999 59 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 168 (Polychromatic418967fa.accept_18_4_15_6_1_3994 58 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 168 3 19 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 105 168 7 8 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 105 168 (Polychromatic418967fa.accept_16_7_9_8_1_829
  55 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 168 3 18 35 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 168
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 168 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 168 3 17 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 168 (Polychromatic418967fa.accept_13_11_1_12_1_742
  50 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 105 168 7 7 15 24
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 105 168 3 16 35
  56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 168
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 168 (Polychromatic418967fa.accept_17_12_3_15_1_5476 46 105 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 168 3 15 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 168
  (Polychromatic418967fa.accept_13_5_1_12_1_740 44 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 168 21 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 168 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 105 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 168
  (Polychromatic418967fa.accept_18_4_15_6_1_3994 40 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 105 168 3 13 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 168 (Polychromatic418967fa.accept_23_15_13_7_1_9389 38 105 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 168
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 168 3 12 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 105 168 7 5 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 105 168 (Polychromatic418967fa.accept_13_8_1_12_1_762 34 105 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 168 3 11 35 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 168
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 168 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 168 3 10 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 168
  (Polychromatic418967fa.accept_17_12_3_15_1_5476 29 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 105 168 7 4 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 105 168 3 9 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 105 168 (Polychromatic418967fa.accept_19_7_10_16_1_9388 26 105 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 168
  (Polychromatic418967fa.accept_19_6_10_16_1_7989 25 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 105 168 3 8 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 105 168 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 105 168 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 168
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 168 21 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 105 168 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 168 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 105
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 168 3 6 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 168
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 168 (Polychromatic418967fa.accept_18_16_15_6_1_4039 16 105 168 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 168 3 5 35 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 105 168 7 2 15 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 105 168
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 168 3 4 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 168 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 168 (Polychromatic418967fa.accept_18_10_15_6_1_6621 10 105
  168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 168 3 3 35 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 168
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 105 168 7 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 105 168 3 2 35 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 168 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 168 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 105 168
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 168 3 1 35 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 168
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 105 168 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 168 (Polychromatic418967fa.accept_16_1_9_8_1_2438 1 105 168 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 168))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_168_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


