-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch150
-- name    : Polychromatic418967fa_Branch150
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:27.019296+00:00
-- url     : https://prove2.me/theorems/49c3d6c2-37d2-4bdd-9032-1eefec584bea
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch150_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_150 : allB 150 150 :=
  allB_succ' 2 149 150 (Eq.refl Bool.true) (allA_succ_of_accept 1 149 150 (accept_3_4 1 149 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 150)) (allB_succ' 3 148 150 (Eq.refl Bool.true) (allA_succ_of_gcd 2 148 150 2 1 74
  75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 148 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 150))) (allB_succ' 4 147 150 (Eq.refl Bool.true) (allA_succ_of_gcd 3 147 150 3 1 49 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 147 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 147 150)))) (allB_succ' 5 146 150 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  146 150 2 2 73 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 146 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 146 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 146 150 2 1 73 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 146 150 (accept_3_4 1 146 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  150))))) (allB_succ' 6 145 150 (Eq.refl Bool.true) (allA_succ_of_gcd 5 145 150 5 1 29 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 150
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 145 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 150 (accept_3_5 2 145 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 150)))))) (allB_succ' 7 144 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 144 150 6 1 24 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 150 (Polychromatic418967fa.accept_19_5_11_17_1_6536 5 144 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 150 2 2 72 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 150 3 1 48 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 150 2 1 72 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 150))))))) (allB_succ' 8 143 150 (Eq.refl
  Bool.true) (allA_succ_of_accept 7 143 150 (accept_3_4 7 143 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 143 150 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 143 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 150 (accept_3_4 4 143 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  143 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 150
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 143 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 150 (accept_3_4 1 143 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  150)))))))) (allB_succ' 9 142 150 (Eq.refl Bool.true) (allA_succ_of_gcd 8 142 150 2 4 71 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 150
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 7 142 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 150 2 3 71 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 150 (accept_3_5 5 142 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  150 2 2 71 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 142 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 150 2 1 71 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 142 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 142 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 150))))))))) (allB_succ' 10 141 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 141 150 3 3 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 150 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 141 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 150 3 2 47 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 141 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 141 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 150 3 1 47 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 141 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 150
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 141 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141 150)))))))))) (allB_succ' 11 140 150 (Eq.refl Bool.true) (allA_succ_of_gcd 10 140 150 10 1 14 15
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 140 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 150 2 4 70 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 150 (accept_3_4 7 140 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  150 2 3 70 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 140
  150 5 1 28 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 140
  150 2 2 70 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  140 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 140 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 140 150 2 1 70 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 140 150 (accept_3_4 1 140 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  150))))))))))) (allB_succ' 12 139 150 (Eq.refl Bool.true) (allA_succ_of_accept 11 139 150 (accept_3_5 11 139 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10
  139 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 150 (accept_3_5 8 139 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 150 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 139 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 150 (accept_3_5 5 139 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 139 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 150 (accept_3_5 2 139 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 150)))))))))))) (allB_succ' 13 138 150 (Eq.refl Bool.true) (allA_succ_of_gcd 12 138 150 6 2
  23 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 150
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 138 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 150 2 5 69 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 138 150 3 3 46 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 138 150 2 4 69 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 138 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 150 6 1 23 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 138 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 150 2 2 69 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 150 3 1 46 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 150 2 1 69 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 138 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 150))))))))))))) (allB_succ' 14 137 150 (Eq.refl Bool.true) (allA_succ_of_accept 13 137 150 (accept_3_4
  13 137 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 150
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 137 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 137 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 150 (accept_3_4 10 137 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 137 150 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 137 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 8
  137 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 150 (accept_3_4 7 137
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 150
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 137 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 137 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 137 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 150 (accept_3_4 4 137 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 137 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 150 (Polychromatic418967fa.accept_16_2_9_6_1_4441
  2 137 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 150 (accept_3_4 1
  137 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137 150)))))))))))))) (allB_succ' 15 136 150 (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 136 150 2 7 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 136 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 136 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 150 2 6 68 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 150 (accept_3_5 11 136 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 150 2 5 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 150 (Polychromatic418967fa.accept_12_9_4_6_1_460 9
  136 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 150 2 4 68 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 150
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 136 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 150 2 3 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 150 (accept_3_5 5 136 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  150 2 2 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 150 2 1 68 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 136 150 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 136 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 150))))))))))))))) (allB_succ' 16 135 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 135 150 15 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 135 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 150 3 4 45 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 150
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 135 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 135 150 5 2 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 135 150 3 3 45 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 135 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 150 (Polychromatic418967fa.accept_18_7_9_6_1_4023 7 135 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 150 3 2 45 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 135 150 5 1 27 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 150
  (Polychromatic418967fa.accept_11_4_3_7_1_828 4 135 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 150 3 1 45 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 135 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135 150)))))))))))))))) (allB_succ' 17 134 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 134 150 2 8 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 134 150 (Polychromatic418967fa.accept_12_3_2_6_1_138 15 134 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 150 2 7 67 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 150 (accept_3_4 13 134 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 150 2 6 67 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 134 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 150 2 5 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 134 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 150 2 4 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 150 (accept_3_4 7 134 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 150 2 3 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 134 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 150 2 2 67 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 3
  134 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 150 2 1 67 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 150 (accept_3_4 1
  134 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 150))))))))))))))))) (allB_succ' 18 133 150 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 133 150 (accept_3_5 17 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 133 150 (Polychromatic418967fa.accept_21_16_7_3_1_8093 16 133 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 150 (accept_3_5 14 133 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 150 (Polychromatic418967fa.accept_9_4_7_6_1_255
  13 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 150
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 150 (accept_3_5 11 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 150 (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 133 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 150 (accept_3_5 8 133 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 150
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 150 (accept_3_5 5 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 133 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 150 (accept_3_5 2 133 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 150 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 150)))))))))))))))))) (allB_succ' 19 132 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 132 150 6 3 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 132 150 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 132 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 150 2 8 66 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 150 3 5 44 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 150 2 7 66 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 150
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 13 132 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 150 6 2 22 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 150 2 5 66 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 150 3 3 44 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 150 2 4 66 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 150 (Polychromatic418967fa.accept_19_7_18_17_1_663
  7 132 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 150 6 1 22 25 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 150
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 132 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 132 150 2 2 66 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 132 150 3 1 44 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 132 150 2 1 66 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 150 (Polychromatic418967fa.accept_17_1_13_14_1_478 1 132 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132 150))))))))))))))))))) (allB_succ' 20 131 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 131 150 (accept_3_4 19 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 150 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 150 (accept_3_4 16 131 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 131 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 150
  (Polychromatic418967fa.accept_11_3_10_7_1_129 14 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 150 (accept_3_4 13 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 131 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 150 (accept_3_4 10 131 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 150 (accept_3_4 7 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 150 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 150 (accept_3_4 4 131 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 131 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 150 (accept_3_4 1 131 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  150)))))))))))))))))))) (allB_succ' 21 130 150 (Eq.refl Bool.true) (allA_succ_of_gcd 20 130 150 10 2 13 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 130 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 150 2 9 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 150 (accept_3_5 17 130 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 150 2 8 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15
  130 150 5 3 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14
  130 150 2 7 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 130 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 130 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 130 150 2 6 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 130 150 (accept_3_5 11 130 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 150 10 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 150 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 130 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 150 2 4 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 7
  130 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 150 2 3 65 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 130 150 5 1 26 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 130 150 2 2 65 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 130 150
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 130 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 130 150 2 1 65 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 130 150 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 130 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 130 150))))))))))))))))))))) (allB_succ' 22 129 150 (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 129 150 3 7 43 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 129 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 150 3 6 43 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 129 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 150 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 129 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 150 3 5 43 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  129 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 129 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 150 3 4 43 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 129 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 150 3 3 43 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 129 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 150 3 2 43 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 150 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 129 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 150
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 129 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 150 3 1 43 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 129 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 129 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 150)))))))))))))))))))))) (allB_succ' 23
  128 150 (Eq.refl Bool.true) (allA_succ_of_gcd 22 128 150 2 11 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 128 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 150 2 10 64 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 150 (accept_3_4 19
  128 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 150 2 9 64 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 128 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 128 150 2 8 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 128 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 128 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 150 2 7 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 150 (accept_3_4 13 128 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 150 2 6 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 150 (Polychromatic418967fa.accept_19_11_14_17_1_6607 11 128
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 150 2 5 64 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 150
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 128 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 150 2 4 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 150 (accept_3_4 7 128 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  150 2 3 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 150 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 128 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 150 2 2 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 128 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 128 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 150 2 1 64 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 150 (accept_3_4 1 128 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 150))))))))))))))))))))))) (allB_succ' 24 127 150 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 127 150 (accept_3_5 23 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 150 (accept_3_5 20 127 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 150
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 150 (accept_3_5 17 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 150 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 150 (Polychromatic418967fa.accept_19_15_13_17_1_5172 15 127 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 150 (accept_3_5 14 127 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 150
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 150 (accept_3_5 11 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 150 (Polychromatic418967fa.accept_21_10_1_3_1_8092 10 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 150 (accept_3_5 8 127 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 150
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 150 (accept_3_5 5 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 127 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 150 (accept_3_5 2 127 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 150)))))))))))))))))))))))) (allB_succ' 25 126 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 126 150 6 4 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 126 150 (Polychromatic418967fa.accept_17_6_7_14_1_6704 23 126 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 150 2 11 63 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 150 3 7 42 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 150 2 10 63 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 150
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 126 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 150 6 3 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 150 (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 126 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 150 2 8 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 150 3 5 42 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 150 2 7 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 150
  (Polychromatic418967fa.accept_22_13_16_18_1_8091 13 126 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 150 6 2 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 150 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 126 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 150 2 5 63 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 150 3 3 42 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 150 2 4 63 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 150
  (Polychromatic418967fa.accept_26_7_22_20_1_8090 7 126 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 150 6 1 21 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 150 (Polychromatic418967fa.accept_19_5_12_17_1_8089 5 126 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 150 2 2 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 150 3 1 42 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 150 2 1 63 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 150 (Polychromatic418967fa.accept_23_1_11_12_1_6314 1 126
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 150)))))))))))))))))))))))))
  (allB_succ' 26 125 150 (Eq.refl Bool.true) (allA_succ_of_gcd 25 125 150 25 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 150
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 24 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 150 (accept_3_4 22 125 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 150 5 4 25 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 150 (accept_3_4 19 125 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 125 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 150
  (Polychromatic418967fa.accept_14_3_13_10_1_761 17 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 150 (accept_3_4 16 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  125 150 5 3 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 125 150 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 150 (accept_3_4 13 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 150 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 125 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 150 5 2 25 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 150 (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 125 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 150 (accept_3_4 7 125 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 150 (Polychromatic418967fa.accept_19_6_11_17_1_2611 6 125 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 150 5 1 25 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 150 (accept_3_4 4 125 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 150 (accept_3_4 1 125 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  150)))))))))))))))))))))))))) (allB_succ' 27 124 150 (Eq.refl Bool.true) (allA_succ_of_gcd 26 124 150 2 13 62 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 150
  (Polychromatic418967fa.accept_20_5_4_10_1_3529 25 124 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 150 2 12 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 150 (accept_3_5 23 124 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 150 2 11 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 124 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 150 2 10 62 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 150
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 124 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 150 2 9 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 150 (accept_3_5 17 124 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 150 2 8 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 124 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 150 2 7 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 150 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 124 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 150 2 6 62 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 150 (accept_3_5 11 124 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 150 2 5 62 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 150
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 150 2 4 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 150 (Polychromatic418967fa.accept_19_7_10_17_1_8088 7 124 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 150 2 3 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 150 (accept_3_5 5 124 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 150 2 2 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 150 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 124 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 150 2 1 62 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  124 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 150)))))))))))))))))))))))))))
  (allB_succ' 28 123 150 (Eq.refl Bool.true) (allA_succ_of_gcd 27 123 150 3 9 41 50 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 150
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 150 3 8 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 150 (Polychromatic418967fa.accept_18_5_15_6_1_3999
  23 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 150 3 7 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 150 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 123 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 150 (Polychromatic418967fa.accept_16_3_11_6_1_4467 19 123
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 150 3 6 41 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 150 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 123 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 150 3 5 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 150 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 150
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 150 3 4 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 150 (Polychromatic418967fa.accept_18_11_15_6_1_2832 11 123 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 150 (Polychromatic418967fa.accept_12_10_3_6_1_882
  10 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 150 3 3 41 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 150
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 150 (Polychromatic418967fa.accept_14_7_11_10_1_2155 7 123 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 150 3 2 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 150
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 123 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 150 3 1 41 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 150 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 123 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 150)))))))))))))))))))))))))))) (allB_succ'
  29 122 150 (Eq.refl Bool.true) (allA_succ_of_gcd 28 122 150 2 14 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 150 (Polychromatic418967fa.accept_12_3_2_6_1_138
  27 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 122 150 2 13 61 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 122 150
  (accept_3_4 25 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 122 150 2 12 61 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 122 150
  (Polychromatic418967fa.accept_17_6_3_14_1_2078 23 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 122 150 2 11 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 122 150 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 122 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 122 150 2 10 61 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 122 150 (accept_3_4 19 122 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 122 150 2 9 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 122 150 (Polychromatic418967fa.accept_9_8_5_6_1_538 17
  122 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 150 2 8 61 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 150
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 150 2 7 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 122 150 (accept_3_4 13 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  122 150 2 6 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 122 150 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 122 150 2 5 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 122 150 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 122 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 150 2 4 61 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 150 (accept_3_4 7 122 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122 150 2 3 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 150 (Polychromatic418967fa.accept_20_5_2_10_1_3576 5 122 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 150 2 2 61 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 150
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 150 2 1 61 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 150 (accept_3_4 1 122 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  150))))))))))))))))))))))))))))) (allB_succ' 30 121 150 (Eq.refl Bool.true) (allA_succ_of_accept 29 121 150
  (accept_3_5 29 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 150
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 150 (accept_3_5 26 121 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 150
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 150 (accept_3_5 23 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 150 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 150 (accept_3_5 20 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 150
  (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 150 (accept_3_5 17 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 150 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 150 (accept_3_5 14 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 150 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 150
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 150 (accept_3_5 11 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 150 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 150 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 150 (accept_3_5 8 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 150
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 150 (accept_3_5 5 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 150 (Polychromatic418967fa.accept_20_4_1_10_1_3643 4 121 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 150 (accept_3_5 2 121 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 150 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 150)))))))))))))))))))))))))))))) (allB_succ' 31 120
  150 (Eq.refl Bool.true) (allA_succ_of_gcd 30 120 150 30 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 150 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 120 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 150 2 14 60 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 150 3 9 40 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 150 2 13 60 75
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 150 5 5 24 30
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 150 6 4 20 25
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 150
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 150 2 11 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 120 150 3 7 40 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 120 150 10 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 120 150 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 150 6 3 20 25 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 150
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 120 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 150 2 8 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 150 15 1 8 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 150 2 7 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 120 150 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 120 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 150 6 2 20 25 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 150 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  120 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 150 10 1 12 15 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 150 3 3 40 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 150 2 4 60 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 150
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 150 6 1 20 25 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 120 150 5 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 120 150 2 2 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 120 150 3 1 40 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 120 150 2 1 60 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 150 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 150))))))))))))))))))))))))))))))) (allB_succ' 32 119 150 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 119 150 (accept_3_4 31 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 119 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 150 (accept_3_4 28 119 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 150 (Polychromatic418967fa.accept_11_5_9_7_1_411
  27 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 150
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 150 (accept_3_4 25 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 150 (Polychromatic418967fa.accept_11_2_9_7_1_124 24 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 150 (accept_3_4 22 119 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 150
  (Polychromatic418967fa.accept_22_20_9_18_1_8087 20 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 119 150 (accept_3_4 19 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 119 150 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 150 (accept_3_4 16 119 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 150
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 119 150 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 150 (accept_3_4 13 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 119 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 119 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 150
  (Polychromatic418967fa.accept_14_11_7_10_1_4852 11 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 119 150 (accept_3_4 10 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 119 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 150 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 119 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 150 (accept_3_4 7 119 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 150
  (Polychromatic418967fa.accept_20_6_19_10_1_3523 6 119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 119 150 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 150 (accept_3_4 4 119 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 119 150 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 150 (Polychromatic418967fa.accept_11_2_9_7_1_124 2
  119 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 150 (accept_3_4 1 119
  150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119 150)))))))))))))))))))))))))))))))) (allB_succ' 33 118 150
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 118 150 2 16 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 118 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 118 150 2 15 59 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 118 150 (accept_3_5 29
  118 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 118 150 2 14 59 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 118 150
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 118 150 2 13 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 118 150 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 118 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 118 150 2 12 59 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 118 150 (accept_3_5 23 118 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 118 150 2 11 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 118 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  118 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 150 2 10 59 75 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 150
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 118 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 150 2 9 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 150 (accept_3_5 17 118 150 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 150 2 8 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 150 (Polychromatic418967fa.accept_11_4_8_7_1_819 15 118 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 150 2 7 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 150 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 118 150 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 150 2 6 59 75 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 150 (accept_3_5 11 118 150
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 150 2 5 59 75 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 150
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 118 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 150 2 4 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 150 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 118 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 150 2 3 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 150 (accept_3_5 5 118 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 150 2 2 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 150 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 118 150 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 150 2 1 59 75 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 150 (Polychromatic418967fa.accept_19_1_4_17_1_5136
  1 118 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  150))))))))))))))))))))))))))))))))) (allB_succ' 34 117 150 (Eq.refl Bool.true) (allA_succ_of_gcd 33 117 150 3 11 39
  50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 150
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 150 3 10 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 150
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 117 150 3 9 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 117 150 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 150 (Polychromatic418967fa.accept_18_7_9_6_1_4023 25 117
  150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 150 3 8 39 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 150 3 7 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 150 (Polychromatic418967fa.accept_12_8_9_6_1_127
  20 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 150
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 150 3 6 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 150 (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 117 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 150 3 5 39 50 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 150
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 150 (Polychromatic418967fa.accept_18_13_9_6_1_4024 13 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 150 3 4 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 150
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 150 3 3 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 150 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 150 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 150 3 2 39 50 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 150
  (Polychromatic418967fa.accept_19_5_3_17_1_6557 5 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 150 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 117 150 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 150 3 1 39 50 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 150 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 117 150
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 150
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 150 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 150))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_150_segment_000)))))))))))))))))))))))))))))))))


