-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch148
-- name    : Polychromatic418967fa_Branch148
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:15:06.803454+00:00
-- url     : https://prove2.me/theorems/50e5fd37-94a2-42fa-b89c-73cd3a0d5c48
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

def Polychromatic418967fa.branch_148 : allB 148 148 :=
  allB_succ' 2 147 148 (Eq.refl Bool.true) (allA_succ_of_accept 1 147 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  147 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 148)) (allB_succ' 3 146 148
  (Eq.refl Bool.true) (allA_of_3_1 3 146 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 145 148 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 145 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 148 (accept_3_3 2 145 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 148 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 145 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 148)))) (allB_succ' 5 144 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 144 148 4 1 36 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 144 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 148 2 1 72 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 148 (Polychromatic418967fa.accept_19_1_11_15_1_2459 1 144
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 148))))) (allB_succ' 6 143 148 (Eq.refl
  Bool.true) (allA_of_3_1 6 143 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 142 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 142 148 2 3 71 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 148 (accept_3_3 5 142 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  148 2 2 71 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 148 2 1 71 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 142 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 142 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 148))))))) (allB_succ' 8 141 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 141 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 141 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 148 (accept_3_3 5 141 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 148 (Polychromatic418967fa.accept_15_4_6_13_1_956
  4 141 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 141 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 148 (accept_3_3 2 141 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 148)))))))) (allB_succ' 9 140 148 (Eq.refl Bool.true) (allA_of_3_1 9 140 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 139 148 (Eq.refl Bool.true) (allA_succ_of_accept 9 139 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 148 (accept_3_3 8 139 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 148 (Polychromatic418967fa.accept_15_6_4_13_1_403 6 139 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 148 (accept_3_3 5 139 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 139 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 148 (accept_3_3 2 139 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 148 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 139 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 148)))))))))) (allB_succ' 11 138 148 (Eq.refl Bool.true) (allA_succ_of_gcd 10 138 148 2 5 69
  74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 138 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 148 2 4 69 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 138 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 148 2 3 69 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 148 (accept_3_3 5 138 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 148 2 2 69 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 138 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 148 2 1 69 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  138 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 148))))))))))) (allB_succ' 12 137
  148 (Eq.refl Bool.true) (allA_of_3_1 12 137 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 136 148
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 136 148 4 3 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 136 148 (accept_3_3 11 136 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 136 148 2 5 68 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 136 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 136 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 148 4 2 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 148 2 3 68 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 148 (accept_3_3 5 136 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 148 4 1 34 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 136 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  136 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 148 2 1 68 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 148
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 136 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 136 148))))))))))))) (allB_succ' 14 135 148 (Eq.refl Bool.true) (allA_succ_of_accept 13 135 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 135 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 135 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 135 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 148 (accept_3_3 11 135 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 135 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 148 (Polychromatic418967fa.accept_19_9_2_15_1_6432
  9 135 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 148 (accept_3_3 8
  135 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 135 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 148 (accept_3_3 5 135 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 135 148 (Polychromatic418967fa.accept_25_4_10_23_1_7934 4 135 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 148 (accept_3_3 2 135 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 148)))))))))))))) (allB_succ' 15 134 148 (Eq.refl Bool.true) (allA_of_3_1 15 134 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 133 148 (Eq.refl Bool.true) (allA_succ_of_accept 15 133 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 148 (accept_3_3 14 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 148 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 148 (accept_3_3 11 133 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 148 (accept_3_3 8 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 148 (Polychromatic418967fa.accept_22_7_1_16_1_7933 7 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 148 (accept_3_3 5 133 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 148 (Polychromatic418967fa.accept_21_4_7_1_1_6307 4 133 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 148 (accept_3_3 2 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 148)))))))))))))))) (allB_succ' 17 132 148 (Eq.refl Bool.true) (allA_succ_of_gcd 16 132 148
  4 4 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132
  148 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 132 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 148 2 7 66 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 148 (Polychromatic418967fa.accept_24_13_12_4_1_2746 13 132 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 148 4 3 33 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 148 (accept_3_3 11
  132 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 148 2 5 66 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 148 4 2 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 132 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 148 2 3 66 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 148 (accept_3_3 5 132 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 148 4 1 33 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 148 2 1 66 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1
  132 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 148))))))))))))))))) (allB_succ' 18
  131 148 (Eq.refl Bool.true) (allA_of_3_1 18 131 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 130 148
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 130 148 2 9 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 130 148 (accept_3_3 17 130 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 148 2 8 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 130 148 (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 130 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 148 2 7 65 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 130 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 148 2 6 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 130 148 (accept_3_3 11 130 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  130 148 2 5 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 130 148 (Polychromatic418967fa.accept_27_9_22_13_1_7932 9 130 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 130 148 2 4 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 130 148 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 130 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 148 2 3 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 148 (accept_3_3 5 130 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130 148 2 2 65 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 130 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 130 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 148 2 1 65 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 130 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 130 148))))))))))))))))))) (allB_succ' 20 129 148 (Eq.refl Bool.true) (allA_succ_of_accept 19 129 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 129 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 129 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 148 (accept_3_3 17 129 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 129 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 129 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 148 (Polychromatic418967fa.accept_9_6_3_4_1_477
  15 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 148 (accept_3_3 14
  129 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 129 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 148 (accept_3_3 11 129 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 129 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 129 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 148 (accept_3_3 8 129
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 148 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 148 (accept_3_3 5 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 148 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 129 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 148 (accept_3_3 2 129 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 148)))))))))))))))))))) (allB_succ' 21 128 148
  (Eq.refl Bool.true) (allA_of_3_1 21 128 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 127 148 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 127 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 148 (accept_3_3 20 127 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 127 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 148
  (Polychromatic418967fa.accept_22_18_17_16_1_4598 18 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 127 148 (accept_3_3 17 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 127 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 127 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 148 (accept_3_3 14 127 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 148
  (Polychromatic418967fa.accept_23_13_12_10_1_7931 13 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 127 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 148 (accept_3_3 11 127 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 148 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 127 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 148 (accept_3_3 8 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 127 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 148 (accept_3_3 5 127 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 148 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 127 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 148 (accept_3_3 2 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 148 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 127 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 148)))))))))))))))))))))) (allB_succ' 23 126 148 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  126 148 2 11 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 126 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 126 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 148 2 10 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 148 (Polychromatic418967fa.accept_15_4_6_13_1_956
  19 126 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 148 2 9 63 74
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 148
  (accept_3_3 17 126 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 148 2 8 63 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 148
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 148 2 7 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 126 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 148 2 6 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 148 (accept_3_3 11 126 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 148 2 5 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 148 2 4 63 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 148
  (Polychromatic418967fa.accept_15_7_6_13_1_936 7 126 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 148 2 3 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 148 (accept_3_3 5 126 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  148 2 2 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 126 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 148 2 1 63 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 126 148 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 126 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 148))))))))))))))))))))))) (allB_succ' 24 125 148 (Eq.refl
  Bool.true) (allA_of_3_1 24 125 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 124 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 124 148 4 6 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 124 148 (accept_3_3 23 124 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  124 148 2 11 62 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 124 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 124 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 148 4 5 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 19
  124 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 148 2 9 62 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 148 (accept_3_3 17
  124 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 148 4 4 31 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 124 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 124 148 2 7 62 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 124 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 124 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 148 4 3 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 148 (accept_3_3 11 124 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 148 2 5 62 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 124 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 124 148 4 2 31 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 124 148
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 7 124 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 124 148 2 3 62 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 124 148 (accept_3_3 5 124 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124
  148 4 1 31 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  124 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 124 148 2 1 62 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 124 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 124 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 148))))))))))))))))))))))))) (allB_succ' 26 123 148 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 123 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 123 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 24
  123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 148 (accept_3_3 23
  123 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 148
  (Polychromatic418967fa.accept_16_6_11_4_1_635 22 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 123 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 148 (accept_3_3 20 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 123 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 123 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 148 (Polychromatic418967fa.accept_12_6_3_4_1_394
  18 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 148 (accept_3_3 17
  123 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 148
  (Polychromatic418967fa.accept_9_7_6_4_1_483 16 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 123 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 148 (accept_3_3 14 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 123 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 123 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 148 (Polychromatic418967fa.accept_7_5_4_1_1_412
  12 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 148 (accept_3_3 11
  123 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 10 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 123 148 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 148 (accept_3_3 8 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 123 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 123 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  6 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 148 (accept_3_3 5
  123 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 148
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 123 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 123 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 148 (accept_3_3 2 123 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 123 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 123 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 148)))))))))))))))))))))))))) (allB_succ' 27 122 148 (Eq.refl
  Bool.true) (allA_of_3_1 27 122 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 121 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 121 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 121 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 148 (accept_3_3 26 121 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 148 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 121 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 148 (accept_3_3 23 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 148 (accept_3_3 20 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 148 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 121 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 148
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 148 (accept_3_3 17 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 148 (Polychromatic418967fa.accept_23_16_6_10_1_7930 16 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 148 (accept_3_3 14 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 148
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 148 (accept_3_3 11 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 148 (accept_3_3 8 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 148 (Polychromatic418967fa.accept_17_7_2_12_1_1069 7 121 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 148 (accept_3_3 5 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 148 (Polychromatic418967fa.accept_17_4_2_12_1_6554 4 121 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 148 (accept_3_3 2 121 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 148 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 121 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 148)))))))))))))))))))))))))))) (allB_succ' 29 120
  148 (Eq.refl Bool.true) (allA_succ_of_gcd 28 120 148 4 7 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 120 148 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 120 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 148 2 13 60 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 120 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 148 4 6 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 148 (accept_3_3 23 120 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  120 148 2 11 60 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 120 148 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 120 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 120 148 4 5 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 19
  120 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 148 2 9 60 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 148 (accept_3_3 17
  120 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 148 4 4 30 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 120 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 120 148 2 7 60 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 120 148 (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 120 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 148 4 3 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 148 (accept_3_3 11 120 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 148 2 5 60 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 148 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 120 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 148 4 2 30 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 120 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 148 2 3 60 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 148 (accept_3_3 5 120 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120
  148 4 1 30 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  120 148 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3 120 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 120 148 2 1 60 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 120 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 120 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 148))))))))))))))))))))))))))))) (allB_succ' 30 119 148
  (Eq.refl Bool.true) (allA_of_3_1 30 119 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 118 148 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 118 148 2 15 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 118 148 (accept_3_3 29 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 148 2 14 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 148 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 118 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 148 2 13 59 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 148
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 148 2 12 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 148 (accept_3_3 23 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 148 2 11 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 118 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 148 2 10 59 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 148 2 9 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 148 (accept_3_3 17 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 148 2 8 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 148 2 7 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 148 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 118 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 148 2 6 59 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 148 (accept_3_3 11 118 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 148 2 5 59 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 118 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 148 2 4 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 118 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 148 2 3 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 148 (accept_3_3 5 118 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 148 2 2 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 118 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 148 2 1 59 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  118 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 148)))))))))))))))))))))))))))))))
  (allB_succ' 32 117 148 (Eq.refl Bool.true) (allA_succ_of_accept 31 117 148 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 148
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 117 148 (accept_3_3 29 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 117 148 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 117 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 148 (accept_3_3 26 117 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 148 (accept_3_3 23 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 117 148 (Polychromatic418967fa.accept_16_6_5_4_1_4330 22 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 148 (Polychromatic418967fa.accept_23_21_2_10_1_7929 21 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 148 (accept_3_3 20 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 117 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 117 148 (accept_3_3 17 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 117 148 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 117 148 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 148 (accept_3_3 14 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 117 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 148
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 148 (accept_3_3 11 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 117 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 148 (accept_3_3 8 117 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 148 (accept_3_3 5 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 117 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 117 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 148 (accept_3_3 2 117 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 117 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 148)))))))))))))))))))))))))))))))) (allB_succ' 33
  116 148 (Eq.refl Bool.true) (allA_of_3_1 33 116 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 115 148
  (Eq.refl Bool.true) (allA_succ_of_accept 33 115 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 148 (accept_3_3 32 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 115 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 148 (accept_3_3 29 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 148 (accept_3_3 26 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 148 (accept_3_3 23 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 148 (accept_3_3 20 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 148
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 148 (accept_3_3 17 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 148 (accept_3_3 14 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 148 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 148 (accept_3_3 11 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 148 (accept_3_3 8 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 148 (accept_3_3 5 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 115 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 148 (accept_3_3 2 115 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 115 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 148)))))))))))))))))))))))))))))))))) (allB_succ' 35
  114 148 (Eq.refl Bool.true) (allA_succ_of_gcd 34 114 148 2 17 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 114 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 114 148 2 16 57 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 148 2 15 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 148 (accept_3_3 29 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 148 2 14 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 114 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 148 2 13 57 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 148
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 148 2 12 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 148 (accept_3_3 23 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 148 2 11 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 114 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 114 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 114 148 2 10 57 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 148
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 148 2 9 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 148 (accept_3_3 17 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  114 148 2 8 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 114 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 114 148 2 7 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 114 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 114 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 148 2 6 57 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 148 (accept_3_3 11 114 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 148 2 5 57 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 114 148
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 114 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 114 148 2 4 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 114 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 148 2 3 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 148 (accept_3_3 5 114 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 114 148 2 2 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 114 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 114 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 148 2 1 57 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1
  114 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  148))))))))))))))))))))))))))))))))))) (allB_succ' 36 113 148 (Eq.refl Bool.true) (allA_of_3_1 36 113 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 112 148 (Eq.refl Bool.true) (allA_succ_of_gcd 36 112 148 4 9 28 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 148
  (accept_3_3 35 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 148 2 17 56 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 148
  (Polychromatic418967fa.accept_19_14_17_15_1_3761 33 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 112 148 4 8 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 112 148 (Polychromatic418967fa.accept_19_12_17_15_1_6460 31 112 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 148 2 15 56 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 148 (accept_3_3 29
  112 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 148 4 7 28 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 148
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 112 148 2 13 56 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 112 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 112 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 112 148 4 6 28 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 112 148 (accept_3_3 23 112 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 112 148 2 11 56 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 112 148 (Polychromatic418967fa.accept_15_6_7_13_1_1666
  21 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 148 4 5 28 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 148
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 148 2 9 56 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 148 (accept_3_3 17 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 148 4 4 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 148 2 7 56 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 148 (Polychromatic418967fa.accept_19_13_17_15_1_7928 13 112 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 148 4 3 28 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 148 (accept_3_3 11
  112 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 148 2 5 56 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 148
  (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 148 4 2 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 148 (Polychromatic418967fa.accept_19_7_17_15_1_6453 7 112 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 148 2 3 56 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 148 (accept_3_3 5 112 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 148 4 1 28 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 148 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 112 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 148 2 1 56 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 148 (Polychromatic418967fa.accept_13_1_8_5_1_2315 1
  112 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  148))))))))))))))))))))))))))))))))))))) (allB_succ' 38 111 148 (Eq.refl Bool.true) (allA_succ_of_gcd 37 111 148 37 1
  3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 36 111 148
  (Polychromatic418967fa.accept_21_15_6_1_1_6306 36 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 111 148 (accept_3_3 35 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 111 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 111 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 111 148 (accept_3_3 32 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 111 148 (accept_3_3 29 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 111 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 111 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 111 148 (accept_3_3 26 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 111 148 (accept_3_3 23 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 111 148 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 111 148 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 111 148 (accept_3_3 20 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 111 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 148
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 111 148 (accept_3_3 17 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 111 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 111 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 111 148 (accept_3_3 14 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 111 148 (accept_3_3 11 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 111 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 111 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 111 148 (accept_3_3 8 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 111 148 (accept_3_3 5 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  111 148 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 111 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 111 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 111 148 (accept_3_3 2 111 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 111 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111 148))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 110 148 (Eq.refl Bool.true) (allA_of_3_1 39 110 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 109 148 (Eq.refl Bool.true) (allA_succ_of_accept 39 109 148 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 148 (accept_3_3 38
  109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 148
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 109 148 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 109 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 148 (accept_3_3 35 109 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 109 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 109 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33
  109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 148 (accept_3_3 32
  109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 109 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 109 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 148 (accept_3_3 29 109 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 109 148 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 148 (accept_3_3 26 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 148 (accept_3_3 23 109 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 148 (accept_3_3 20 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 148 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 148 (accept_3_3 17 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 109 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 148 (accept_3_3 14 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 148 (Polychromatic418967fa.accept_19_13_14_15_1_7924 13 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 148 (accept_3_3 11 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 109 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 148 (accept_3_3 8 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 109 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 148 (accept_3_3 5 109 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 109 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 148 (accept_3_3 2 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 109 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 148)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 108 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 108 148 4 10 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 108 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 148 2 19 54 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 148 4 9 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 148 (accept_3_3 35 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  108 148 2 17 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 108 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 108 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 108 148 4 8 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 148 (Polychromatic418967fa.accept_15_1_3_13_1_2548
  31 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 108 148 2 15 54 74
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 108 148
  (accept_3_3 29 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 148 4 7 27 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 148
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 148 2 13 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 148 4 6 27 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 148 (accept_3_3 23 108 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 148 2 11 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 148 (Polychromatic418967fa.accept_16_5_12_4_1_4325
  21 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 148 4 5 27 37
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 148 2 9 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 148 (accept_3_3 17 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  108 148 4 4 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 108 148 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 148 2 7 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 148 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 108 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 148 4 3 27 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 148 (accept_3_3 11
  108 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 148 2 5 54 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 148 4 2 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 148 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 148 2 3 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 148 (accept_3_3 5 108 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 148 4 1 27 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 148 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 108 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 148 2 1 54 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 148 (Polychromatic418967fa.accept_13_1_4_5_1_113 1
  108 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108
  148))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 107 148 (Eq.refl Bool.true) (allA_of_3_1 42 107 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 106 148 (Eq.refl Bool.true) (allA_succ_of_gcd 42 106 148 2 21
  53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 106 148
  (accept_3_3 41 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 106 148 2 20 53 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 106 148
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 106 148 2 19 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 106 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 106 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 106 148 2 18 53 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 106 148 (accept_3_3 35 106 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 106 148 2 17 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 106 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 148 2 16 53 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 148
  (Polychromatic418967fa.accept_11_9_7_5_1_749 31 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 148 2 15 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 148 (accept_3_3 29 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 148 2 14 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 148 (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 106 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 148 2 13 53 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 148 2 12 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 148 (accept_3_3 23 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 148 2 11 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 106 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 148 2 10 53 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 148
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 148 2 9 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 148 (accept_3_3 17 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 148 2 8 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 148 2 7 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 106 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 148 2 6 53 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 148 (accept_3_3 11 106 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 148 2 5 53 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 148
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 148 2 4 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 106 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 148 2 3 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 148 (accept_3_3 5 106 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 148 2 2 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 106 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 148 2 1 53 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1
  106 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  148))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 105 148 (Eq.refl Bool.true) (allA_succ_of_accept 43 105
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 105 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 105 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 105 148 (accept_3_3 41 105 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 105 148 (Polychromatic418967fa.accept_16_8_9_4_1_630 40 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 105 148 (accept_3_3 38 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 105 148 (Polychromatic418967fa.accept_19_17_10_15_1_7927 36 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 105 148 (accept_3_3 35 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 105 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 148
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 105 148 (accept_3_3 32 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 105 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 105 148 (accept_3_3 29 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 148
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 148 (accept_3_3 26 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 105 148 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 105 148 (accept_3_3 23 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 105
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 148
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 105 148 (accept_3_3 20 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 105 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 148 (accept_3_3 17 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 148
  (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 105 148 (accept_3_3 14 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 105 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 105 148 (accept_3_3 11 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 148
  (Polychromatic418967fa.accept_13_9_1_5_1_964 9 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 105 148 (accept_3_3 8 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 105 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 105 148 (accept_3_3 5 105 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 148 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 105 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 105 148 (accept_3_3 2 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  105 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 105 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 105 148)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 104 148 (Eq.refl Bool.true)
  (allA_of_3_1 45 104 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 103 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 45 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 103 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 148 (accept_3_3 44 103 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 103 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 148 (Polychromatic418967fa.accept_19_4_8_15_1_585
  42 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 148 (accept_3_3 41
  103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 148
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 103 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 148 (accept_3_3 38 103 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 103 148 (Polychromatic418967fa.accept_21_16_19_1_1_6320 37 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 148
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 148 (accept_3_3 35 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 148 (accept_3_3 32 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 148
  (Polychromatic418967fa.accept_13_4_12_5_1_476 30 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 148 (accept_3_3 29 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 148 (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 148 (accept_3_3 26 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 148 (accept_3_3 23 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 148 (accept_3_3 20 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 148 (accept_3_3 17 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 148 (accept_3_3 14 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 148
  (Polychromatic418967fa.accept_16_12_7_4_1_687 12 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 148 (accept_3_3 11 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 148 (accept_3_3 8 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 148 (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 148 (accept_3_3 5 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 103 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 148 (accept_3_3 2 103 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 148 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 103 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103 148))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 47 102 148 (Eq.refl Bool.true) (allA_succ_of_gcd 46 102 148 2 23 51 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 148 2 22 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 102 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 148 2 21 51 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 148 (accept_3_3 41 102 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 148 2 20 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 148 (Polychromatic418967fa.accept_12_3_6_4_1_400
  39 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 102 148 2 19 51 74
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 148
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 148 2 18 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 148 (accept_3_3 35 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 102 148 2 17 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 102 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 102 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 102 148 2 16 51 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 148 2 15 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 148 (accept_3_3 29 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 102 148 2 14 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 102 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 102 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 102 148 2 13 51 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 148 2 12 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 148 (accept_3_3 23 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 102 148 2 11 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 102 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 102 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 102 148 2 10 51 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 148 2 9 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 148 (accept_3_3 17 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  102 148 2 8 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 102 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 102 148 2 7 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 102 148 (Polychromatic418967fa.accept_16_13_6_4_1_3277 13 102 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 148 2 6 51 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 148 (accept_3_3 11 102 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 148 2 5 51 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 102 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 102 148 2 4 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 102 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 148 2 3 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 148 (accept_3_3 5 102 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 102 148 2 2 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 102 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 102 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 148 2 1 51 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1
  102 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  148))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 101 148 (Eq.refl Bool.true) (allA_of_3_1 48 101 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 100 148 (Eq.refl Bool.true) (allA_succ_of_gcd 48 100 148 4 12
  25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 100 148
  (accept_3_3 47 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 100 148 2 23 50 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 100 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 100 148 4 11 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 100 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 100 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 148 2 21 50 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 148 (accept_3_3 41 100 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 148 4 10 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 39
  100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 100 148 2 19 50 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 100 148
  (Polychromatic418967fa.accept_17_3_15_12_1_5353 37 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 100 148 4 9 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 100 148 (accept_3_3 35 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 100 148 2 17 50 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 100 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 100 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 100 148 4 8 25 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 100 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 100 148 2 15 50 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 100 148 (accept_3_3 29 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 100 148 4 7 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 100 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 100 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 148 2 13 50 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 25
  100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 100 148 4 6 25 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 100 148 (accept_3_3 23
  100 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 100 148 2 11 50 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 100 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 100 148 4 5 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 100 148 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 100 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 148 2 9 50 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 148 (accept_3_3 17 100 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 148 4 4 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 15
  100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 100 148 2 7 50 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 100 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 100 148 4 3 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 100 148 (accept_3_3 11 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 148 2 5 50 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 148 (Polychromatic418967fa.accept_19_9_5_15_1_2544 9 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 100 148 4 2 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 100 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 100 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 100 148 2 3 50 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 100 148 (accept_3_3 5 100 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100 148 4 1 25 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 100 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 100 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 100 148 2 1 50 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 100 148
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 100 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 100 148))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 99 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 99 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 99 148 (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 99
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 99 148 (accept_3_3 47 99 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 148 (Polychromatic418967fa.accept_19_8_4_15_1_1414
  46 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 148
  (Polychromatic418967fa.accept_17_11_14_12_1_2995 45 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 148 (accept_3_3 44 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 99 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 99 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 148 (accept_3_3 41 99 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 148 (Polychromatic418967fa.accept_13_1_8_5_1_2315
  40 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 148
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 148 (accept_3_3 38 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 148 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 99 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 148 (accept_3_3 35 99 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 99 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 148
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 148 (accept_3_3 32 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 148 (accept_3_3 29 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 148 (Polychromatic418967fa.accept_16_12_3_4_1_4317 28 99 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 148
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 148 (accept_3_3 26 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 148 (accept_3_3 23 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 148 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 99 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 148
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 148 (accept_3_3 20 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 148 (accept_3_3 17 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 148 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 99 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 148
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 148 (accept_3_3 14 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 148 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 148 (accept_3_3 11 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 148 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 99 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 148
  (Polychromatic418967fa.accept_14_9_1_8_1_2849 9 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 148 (accept_3_3 8 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 99 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 99 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 148 (accept_3_3 5 99 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 99 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 99 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 148 (Polychromatic418967fa.accept_13_3_8_5_1_974 3
  99 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 148 (accept_3_3 2 99 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 99
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  148)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 98 148 (Eq.refl Bool.true) (allA_of_3_1 51 98 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 97 148 (Eq.refl Bool.true) (allA_succ_of_accept 51 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 97 148 (accept_3_3 50 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  97 148 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 97 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 48 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 97 148 (accept_3_3 47 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 97 148 (accept_3_3 44 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  97 148 (Polychromatic418967fa.accept_13_4_6_5_1_2333 43 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 97 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 148 (accept_3_3 41 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 97 148 (accept_3_3 38 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  97 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 97 148 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 97 148 (accept_3_3 35 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 97 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 97 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 97 148 (accept_3_3 32 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  97 148 (Polychromatic418967fa.accept_18_13_7_4_1_2738 31 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 97 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 97 148 (accept_3_3 29 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 97 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 97 148 (accept_3_3 26 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  97 148 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 97 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 97 148 (accept_3_3 23 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 97 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 97 148 (accept_3_3 20 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  97 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 97 148 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 97 148 (accept_3_3 17 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 97 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 97 148 (accept_3_3 14 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  97 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 97 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 97 148 (accept_3_3 11 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 97 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 97 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 97 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 97 148 (accept_3_3 8 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 97
  148 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 97 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 97 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 97 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 97 148 (accept_3_3 5 97 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 97 148 (Polychromatic418967fa.accept_13_4_6_5_1_2333 4 97 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 97 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 97
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 148 (accept_3_3 2 97 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 97
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97
  148)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 96 148 (Eq.refl Bool.true) (allA_succ_of_gcd 52
  96 148 4 13 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  51 96 148 (Polychromatic418967fa.accept_18_15_6_4_1_5147 51 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 96 148 2 25 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 96 148 (Polychromatic418967fa.accept_15_4_6_13_1_956 49 96 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 148 4 12 24 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 148 (accept_3_3 47 96 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 148 2 23 48 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 96 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 96 148 4 11 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 96 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 96 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 148 2 21 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 148 (accept_3_3 41 96 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 148 4 10 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 96 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 148 2 19 48 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 148
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 96 148 4 9 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 96 148 (accept_3_3 35 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96
  148 2 17 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  96 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 96 148 4 8 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 96 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 96 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 148 2 15 48 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 148 (accept_3_3 29 96 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 148 4 7 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 96 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 96 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 148 2 13 48 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 148 4 6 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 148 (accept_3_3 23 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96
  148 2 11 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  96 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 96 148 4 5 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 96 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 96 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 148 2 9 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 148 (accept_3_3 17 96 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 96 148 4 4 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 96 148 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 96 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 148 2 7 48 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 96 148 4 3 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 96 148 (accept_3_3 11 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96
  148 2 5 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  96 148 (Polychromatic418967fa.accept_21_9_12_1_1_7926 9 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 96 148 4 2 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 96 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 96 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 148 2 3 48 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96 148 (accept_3_3 5 96 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 148 4 1 24 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 96 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 96 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 148 2 1 48 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 148
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 96 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 96 148))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 95 148 (Eq.refl Bool.true)
  (allA_of_3_1 54 95 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 94 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 94 148 2 27 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 94 148 (accept_3_3 53 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 94
  148 2 26 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  94 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 94 148 2 25 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 94 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 94 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 94 148 2 24 47 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 94 148 (accept_3_3 47 94 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94 148 2 23 47 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 94 148
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 94 148 2 22 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 94 148 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 94 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 148 2 21 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 148 (accept_3_3 41 94 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 148 2 20 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 94 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 94 148 2 19 47 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 94 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 94 148 2 18 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 94 148 (accept_3_3 35 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94
  148 2 17 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  94 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 94 148 2 16 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 94 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 94 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 94 148 2 15 47 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 94 148 (accept_3_3 29 94 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94 148 2 14 47 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 94 148
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 94 148 2 13 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 94 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 94 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 148 2 12 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 148 (accept_3_3 23 94 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 148 2 11 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 148 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 94 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 94 148 2 10 47 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 94 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 94 148 2 9 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 94 148 (accept_3_3 17 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 94
  148 2 8 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  94 148 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 94 148 2 7 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 94 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 94 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 148 2 6 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 148 (accept_3_3 11 94 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 148 2 5 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 94 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 94 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 94 148 2 4 47 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 94 148
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 94 148 2 3 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 94 148 (accept_3_3 5 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 94 148
  2 2 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 94
  148 (Polychromatic418967fa.accept_19_3_18_15_1_3711 3 94 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 94 148 2 1 47 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 94 148 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 94 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 93 148 (Eq.refl Bool.true) (allA_succ_of_accept 55 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 148
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 148 (accept_3_3 53 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  93 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 148 (accept_3_3 50 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 48 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 148 (accept_3_3 47 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  93 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 148 (accept_3_3 44 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 148 (accept_3_3 41 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  93 148 (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 148 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 148 (accept_3_3 38 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 93 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 148
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 148 (accept_3_3 35 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  93 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 148 (accept_3_3 32 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 148
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 148 (accept_3_3 29 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  93 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 148 (accept_3_3 26 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 148 (accept_3_3 23 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  93 148 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 148 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 148 (accept_3_3 20 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 93 148
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 93 148 (accept_3_3 17 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  93 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 93 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 148 (accept_3_3 14 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 93 148
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 93 148 (accept_3_3 11 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  93 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 93 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 148 (accept_3_3 8 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 148 (accept_3_3 5 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93
  148 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 93 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 148 (accept_3_3 2 93 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 93 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 92 148 (Eq.refl Bool.true) (allA_of_3_1 57
  92 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 91 148 (Eq.refl Bool.true) (allA_succ_of_accept 57 91
  148 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 91 148 (accept_3_3 56 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  91 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 91 148 (Polychromatic418967fa.accept_16_6_11_4_1_635 54 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 91 148 (accept_3_3 53 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 91 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 91 148 (accept_3_3 50 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  91 148 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 91 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 91 148 (accept_3_3 47 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 91 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 91 148 (accept_3_3 44 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  91 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 91 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 91 148 (accept_3_3 41 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 91 148 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 91 148 (accept_3_3 38 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  91 148 (Polychromatic418967fa.accept_20_17_11_8_1_4894 37 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 91 148 (Polychromatic418967fa.accept_17_2_6_12_1_7912 36 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 91 148 (accept_3_3 35 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 91 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 91 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 91 148 (accept_3_3 32 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  91 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 91 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 91 148 (accept_3_3 29 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 91 148 (Polychromatic418967fa.accept_16_12_11_4_1_1359 28 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 91 148 (accept_3_3 26 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  91 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 91 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 91 148 (accept_3_3 23 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 91 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 91 148 (accept_3_3 20 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  91 148 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 91 148 (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 91 148 (accept_3_3 17 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 91 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 91 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 91 148 (accept_3_3 14 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  91 148 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 91 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 91 148 (accept_3_3 11 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 91 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 91 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 91 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 91 148 (accept_3_3 8 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 91
  148 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 91 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 91 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 91 148 (accept_3_3 5 91 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 91 148 (Polychromatic418967fa.accept_21_4_7_1_1_6307 4 91 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 91 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 91
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 148 (accept_3_3 2 91 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 148 (Polychromatic418967fa.accept_14_1_7_8_1_2063 1
  91 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 90 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 90 148 2 29 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 90 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 90 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 90 148 2 28 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90 148
  (Polychromatic418967fa.accept_19_17_14_15_1_1403 55 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 90 148 2 27 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 90 148 (accept_3_3 53 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 90 148 2 26 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 90 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 90 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 148 2 25 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 148 (Polychromatic418967fa.accept_14_7_6_8_1_2856
  49 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 148 2 24 45 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 148 (accept_3_3 47
  90 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 90 148 2 23 45 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 90 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 90 148 2 22 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 148 (Polychromatic418967fa.accept_13_4_12_5_1_476 43 90 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 148 2 21 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 148 (accept_3_3 41 90 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 148 2 20 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 90 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 90 148 2 19 45 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 148 2 18 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 148 (accept_3_3 35 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90
  148 2 17 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  90 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 90 148 2 16 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 90 148 (Polychromatic418967fa.accept_22_9_2_16_1_6152 31 90 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 148 2 15 45 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 148 (accept_3_3 29 90 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 90 148 2 14 45 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 90 148
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 90 148 2 13 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 148 (Polychromatic418967fa.accept_17_8_5_12_1_7925 25 90 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 148 2 12 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 148 (accept_3_3 23 90 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 148 2 11 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 90 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 148 2 10 45 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 148 2 9 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 148 (accept_3_3 17 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90
  148 2 8 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  90 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 90 148 2 7 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 90 148 (Polychromatic418967fa.accept_19_13_14_15_1_7924 13 90 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 148 2 6 45 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 148 (accept_3_3 11 90 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 148 2 5 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 90 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 148 2 4 45 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 148
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 90 148 2 3 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 90 148 (accept_3_3 5 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 148
  2 2 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90
  148 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 90 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 148 2 1 45 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 148 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 90 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 90 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 60 89 148 (Eq.refl Bool.true) (allA_of_3_1 60 89 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  61 88 148 (Eq.refl Bool.true) (allA_succ_of_gcd 60 88 148 4 15 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 88 148 (accept_3_3 59 88 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 88 148 2 29 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 88 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 88 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 88 148 4 14 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 148
  (Polychromatic418967fa.accept_9_1_7_4_1_52 55 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 148 2 27 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 88 148 (accept_3_3 53 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88
  148 4 13 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  88 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 88 148 2 25 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 88 148 (Polychromatic418967fa.accept_16_1_8_4_1_4334 49 88 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 148 4 12 22 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 148 (accept_3_3 47 88 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 148 2 23 44 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 88 148 4 11 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 88 148 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 88 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 88 148 2 21 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 88 148 (accept_3_3 41 88 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88 148 4 10 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 88 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 88 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 88 148 2 19 44 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 88 148
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 88 148 4 9 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 88 148 (accept_3_3 35 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88
  148 2 17 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  88 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 88 148 4 8 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 88 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 88 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 88 148 2 15 44 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 88 148 (accept_3_3 29 88 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88 148 4 7 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 88 148 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 88 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 88 148 2 13 44 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 88 148
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 88 148 4 6 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 88 148 (accept_3_3 23 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88
  148 2 11 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  88 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 148 4 5 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 88 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 148 2 9 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 148 (accept_3_3 17 88 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 148 4 4 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 88 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 88 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 148 2 7 44 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 148
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 13 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 148 4 3 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 148 (accept_3_3 11 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  148 2 5 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 148 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 148 4 2 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 148 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 88 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 148 2 3 44 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 148 (accept_3_3 5 88 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 148 4 1 22 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 88 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 148 2 1 44 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 148
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 88 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 87 148 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 87 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 87 148 (accept_3_3 59 87
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 148 (Polychromatic418967fa.accept_7_2_3_1_1_10
  58 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 87 148 (accept_3_3 56 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 87 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 148 (accept_3_3 53 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 148 (accept_3_3 50 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 148 (accept_3_3 47 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 148
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 148 (accept_3_3 44 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 148 (accept_3_3 41 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 148
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 148 (accept_3_3 38 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 148 (Polychromatic418967fa.accept_21_15_3_1_1_6338 36 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 148 (accept_3_3 35 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 87 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 148 (accept_3_3 32 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 87 148 (accept_3_3 29 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 148
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 148 (accept_3_3 26 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 148 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 148 (accept_3_3 23 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 148 (Polychromatic418967fa.accept_26_22_9_18_1_7923 22 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 148 (accept_3_3 20 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 148 (accept_3_3 17 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 148
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 148 (accept_3_3 14 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 148 (accept_3_3 11 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 87 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 148 (accept_3_3 8 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 87 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 148 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 87 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 148 (accept_3_3 5 87 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 87 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 148 (accept_3_3 2 87 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 87
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 86 148 (Eq.refl Bool.true)
  (allA_of_3_1 63 86 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 85 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 85 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 85 148 (accept_3_3 62 85 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 85 148 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 85 148
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 85 148 (accept_3_3 59 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 148 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 148 (accept_3_3 56 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 148 (Polychromatic418967fa.accept_20_15_5_8_1_4920 55 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 148
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 148 (accept_3_3 53 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 148 (accept_3_3 50 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 148
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 48 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 148 (accept_3_3 47 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 148 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 148 (accept_3_3 44 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 148 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 148
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 148 (accept_3_3 41 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 148 (Polychromatic418967fa.accept_16_8_5_4_1_674 40 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 148 (accept_3_3 38 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 148 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 148
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 148 (accept_3_3 35 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 148 (accept_3_3 32 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 148 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 148
  (Polychromatic418967fa.accept_14_2_1_8_1_650 30 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 148 (accept_3_3 29 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 148 (Polychromatic418967fa.accept_13_2_7_5_1_3189 28 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 148 (accept_3_3 26 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 148
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 148 (accept_3_3 23 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 148 (accept_3_3 20 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 148 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 148
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 148 (accept_3_3 17 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 148 (Polychromatic418967fa.accept_14_2_1_8_1_650 16 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 148 (accept_3_3 14 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 148 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 148
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 148 (accept_3_3 11 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 148 (accept_3_3 8 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 148 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 148
  (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 148 (accept_3_3 5 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  148 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 85 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 148 (accept_3_3 2 85 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 85 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 84 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 84 148 4 16 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 148 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 84 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 148 2 31 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 61
  84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 148 4 15 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 148 (accept_3_3 59
  84 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 148 2 29 42 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 148
  (Polychromatic418967fa.accept_22_13_18_16_1_1756 57 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 84 148 4 14 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 84 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 55 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 148 2 27 42 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 148 (accept_3_3 53 84 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 84 148 4 13 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 84 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 51 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 84 148 2 25 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 84 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 84 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 148 4 12 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 148 (accept_3_3 47 84 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 148 2 23 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 148 (Polychromatic418967fa.accept_17_11_16_12_1_1984 45 84
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 148 4 11 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 148 2 21 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 148 (accept_3_3 41 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84
  148 4 10 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  84 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 84 148 2 19 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 84 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 37 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 148 4 9 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 148 (accept_3_3 35 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 84 148 2 17 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 84 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 33
  84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 148 4 8 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 148
  (Polychromatic418967fa.accept_11_9_7_5_1_749 31 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 84 148 2 15 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 84 148 (accept_3_3 29 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84
  148 4 7 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  84 148 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 84 148 2 13 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 84 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 148 4 6 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 148 (accept_3_3 23 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 148 2 11 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 148 (Polychromatic418967fa.accept_19_2_8_15_1_2447
  21 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 148 4 5 21 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 148
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 84 148 2 9 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 84 148 (accept_3_3 17 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84
  148 4 4 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  84 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 84 148 2 7 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 84 148 (Polychromatic418967fa.accept_17_13_16_12_1_6562 13 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 148 4 3 21 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 148 (accept_3_3 11 84 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 148 2 5 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 84 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 148 4 2 21 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 148 2 3 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 148 (accept_3_3 5 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 148
  4 1 21 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84
  148 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 84 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 84 148 2 1 42 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 84 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 84 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 83 148 (Eq.refl Bool.true)
  (allA_of_3_1 66 83 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 82 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 82 148 2 33 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 82 148 (accept_3_3 65 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 82
  148 2 32 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  82 148 (Polychromatic418967fa.accept_25_13_7_23_1_7922 63 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 82 148 2 31 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 82 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 82 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 148 2 30 41 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 148 (accept_3_3 59 82 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 148 2 29 41 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 57 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 82 148 2 28 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 82 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 82 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 82 148 2 27 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 82 148 (accept_3_3 53 82 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82 148 2 26 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 82 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 82 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 148 2 25 41 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 148 2 24 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 82 148 (accept_3_3 47 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82
  148 2 23 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  82 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 82 148 2 22 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 82 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 82 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 148 2 21 41 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 148 (accept_3_3 41 82 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 148 2 20 41 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 82 148 2 19 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 82 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 82 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 148 2 18 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 148 (accept_3_3 35 82 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 148 2 17 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 82 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 148 2 16 41 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 148 2 15 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 148 (accept_3_3 29 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  148 2 14 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 148 2 13 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 82 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 148 2 12 41 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 148 (accept_3_3 23 82 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 148 2 11 41 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 148 2 10 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 82 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 148 2 9 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 148 (accept_3_3 17 82 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 148 2 8 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 82 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 148 2 7 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 13
  82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 148 2 6 41 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 148 (accept_3_3 11
  82 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 148 2 5 41 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 148
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 148 2 4 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 82 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 148 2 3 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 148 (accept_3_3 5 82 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 148 2 2 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 82 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 148 2 1 41 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  82 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 81 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 81 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 81 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 81 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 81 148 (accept_3_3 65 81 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 148 (Polychromatic418967fa.accept_15_4_6_13_1_956
  64 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 148
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 81 148 (accept_3_3 62 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 81 148 (Polychromatic418967fa.accept_13_8_3_5_1_1636 60 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 81 148 (accept_3_3 59 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 148 (Polychromatic418967fa.accept_13_6_3_5_1_3167 58 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 148
  (Polychromatic418967fa.accept_21_15_18_1_1_6300 57 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 81 148 (accept_3_3 56 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 81 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 81 148 (accept_3_3 53 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 148
  (Polychromatic418967fa.accept_16_3_1_4_1_5426 51 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 81 148 (accept_3_3 50 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 81 148 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 81 148 (accept_3_3 47 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 148 (Polychromatic418967fa.accept_14_4_11_8_1_2034 46 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 81 148 (accept_3_3 44 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 81 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 81 148 (accept_3_3 41 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 148
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 81 148 (accept_3_3 38 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 81 148 (Polychromatic418967fa.accept_19_17_5_15_1_7921 36 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 81 148 (accept_3_3 35 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 148 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 81 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 81 148 (accept_3_3 32 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 81 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 148 (accept_3_3 29 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 148 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 148
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 81 148 (accept_3_3 26 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 81 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 81 148 (accept_3_3 23 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 148 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 148
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 81 148 (accept_3_3 20 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 81 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 81 148 (accept_3_3 17 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 148 (Polychromatic418967fa.accept_17_16_13_12_1_4092 16 81 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 148
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 81 148 (accept_3_3 14 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 81 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 148 (accept_3_3 11 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 81 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 148
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 81 148 (accept_3_3 8 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 81 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 81 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 81 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 81 148 (accept_3_3 5 81 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 81 148 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 81 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 81 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 81
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 148 (accept_3_3 2 81 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 81
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 80 148 (Eq.refl Bool.true)
  (allA_of_3_1 69 80 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 79 148 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 79 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 79 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 79 148 (accept_3_3 68 79 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 79 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 79 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 66
  79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 148 (accept_3_3 65 79
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 79 148 (Polychromatic418967fa.accept_9_1_7_4_1_52
  64 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 148 (accept_3_3 62 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 148 (Polychromatic418967fa.accept_10_1_9_8_1_123 61 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 60 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 148 (accept_3_3 59 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 148 (accept_3_3 56 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 148 (accept_3_3 53 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 148 (accept_3_3 50 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 148 (Polychromatic418967fa.accept_18_13_7_4_1_2738 49 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 148 (accept_3_3 47 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 148 (accept_3_3 44 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 148 (accept_3_3 41 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 148 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 148 (accept_3_3 38 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 148 (Polychromatic418967fa.accept_15_6_4_13_1_403 36 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 148 (accept_3_3 35 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 148 (accept_3_3 32 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 148 (accept_3_3 29 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 148 (accept_3_3 26 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 148 (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 148 (accept_3_3 23 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 148 (accept_3_3 20 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 148 (Polychromatic418967fa.accept_19_18_3_15_1_3765 18 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 148 (accept_3_3 17 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 148 (Polychromatic418967fa.accept_13_3_1_5_1_499 16 79 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 148 (accept_3_3 14 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 148 (accept_3_3 11 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 148 (accept_3_3 8 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  148 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 148 (accept_3_3 5 79 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 79 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 148 (accept_3_3 2 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 79 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 79 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 78 148 (Eq.refl
  Bool.true) (allA_succ_of_gcd 70 78 148 2 35 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 78 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 78 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 148 2 34 39 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 148
  (Polychromatic418967fa.accept_22_1_12_16_1_6178 67 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 78 148 2 33 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 78 148 (accept_3_3 65 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78
  148 2 32 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63
  78 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 78 148 2 31 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 78 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 61 78 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 148 2 30 39 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 148 (accept_3_3 59 78 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 148 2 29 39 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 78 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 57 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 78 148 2 28 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 78 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 55 78 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 148 2 27 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 148 (accept_3_3 53 78 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 148 2 26 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 78 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 148 2 25 39 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 148
  (Polychromatic418967fa.accept_16_1_14_4_1_3220 49 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 78 148 2 24 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 78 148 (accept_3_3 47 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78
  148 2 23 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  78 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 78 148 2 22 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 78 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 78 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 148 2 21 39 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 148 (accept_3_3 41 78 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 148 2 20 39 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 78 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 78 148 2 19 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 78 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 78 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 148 2 18 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 148 (accept_3_3 35 78 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 148 2 17 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 78 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 148 2 16 39 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 148
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 148 2 15 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 148 (accept_3_3 29 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78
  148 2 14 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  78 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 78 148 2 13 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 78 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 78 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 148 2 12 39 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 148 (accept_3_3 23 78 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 78 148 2 11 39 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 78 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 78 148 2 10 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 78 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 148 2 9 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 148 (accept_3_3 17 78 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 78 148 2 8 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 78 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 78 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 78 148 2 7 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 148 (Polychromatic418967fa.accept_19_13_2_15_1_7920
  13 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78 148 2 6 39 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 78 148 (accept_3_3 11
  78 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 148 2 5 39 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 78 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 78 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 78 148 2 4 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 78 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 78 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 148 2 3 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 148 (accept_3_3 5 78 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 78 148 2 2 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 78 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 78 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 78 148 2 1 39 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 78 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 78
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 77 148 (Eq.refl Bool.true)
  (allA_of_3_1 72 77 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 76 148 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 76 148 4 18 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 76 148 (accept_3_3 71 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 76
  148 2 35 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69
  76 148 (Polychromatic418967fa.accept_16_5_12_4_1_4325 69 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 76 148 4 17 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 76 148 (Polychromatic418967fa.accept_16_3_12_4_1_170 67 76 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 148 2 33 38 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 148 (accept_3_3 65 76 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 148 4 16 19 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 148
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 76 148 2 31 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 76 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 61 76 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 148 4 15 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 148 (accept_3_3 59 76 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 148 2 29 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 148 (Polychromatic418967fa.accept_15_12_1_13_1_3444 57 76
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 148 4 14 19 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 148
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 55 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 148 2 27 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 76 148 (accept_3_3 53 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76
  148 4 13 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  76 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 76 148 2 25 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 76 148 (Polychromatic418967fa.accept_14_7_6_8_1_2856 49 76 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 76 148 4 12 19 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 148 (accept_3_3 47 76 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 148 2 23 38 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 148
  (Polychromatic418967fa.accept_13_6_11_5_1_133 45 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 148 4 11 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 76 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 148 2 21 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 148 (accept_3_3 41 76 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 148 4 10 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 148 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 76 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 148 2 19 38 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 148 4 9 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 148 (accept_3_3 35 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  148 2 17 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 148 4 8 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 76 148 (Polychromatic418967fa.accept_16_15_12_4_1_4324 31 76 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 148 2 15 38 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 148 (accept_3_3 29 76 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 148 4 7 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 148 (Polychromatic418967fa.accept_15_12_1_13_1_3444
  27 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 148 2 13 38 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 148
  (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 148 4 6 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 148 (accept_3_3 23 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  148 2 11 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  76 148 (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 148 4 5 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 76 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 148 2 9 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 148 (accept_3_3 17 76 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 148 4 4 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 76 148 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 76 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 148 2 7 38 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 148
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 148 4 3 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 148 (accept_3_3 11 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  148 2 5 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 148 4 2 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 148 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 76 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 148 2 3 38 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 148 (accept_3_3 5 76 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 148 4 1 19 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 76 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 148 2 1 38 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 148
  (Polychromatic418967fa.accept_16_1_12_4_1_695 1 76 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 75 148
  (Eq.refl Bool.true) (allA_succ_of_accept 73 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 75 148
  (Polychromatic418967fa.accept_10_2_5_8_1_139 72 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 75 148 (accept_3_3 71 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  75 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 75 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 148 (accept_3_3 68 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 75 148 (accept_3_3 65 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  75 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 75 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 148 (accept_3_3 62 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 75 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 75 148 (accept_3_3 59 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  75 148 (Polychromatic418967fa.accept_13_6_10_5_1_1648 58 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 75 148 (Polychromatic418967fa.accept_10_7_5_8_1_1167 57 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 148 (accept_3_3 56 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 75 148
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 75 148 (accept_3_3 53 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  75 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 75 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 148 (accept_3_3 50 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 75 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 75 148 (accept_3_3 47 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  75 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 75 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 148 (accept_3_3 44 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 148 (accept_3_3 41 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  75 148 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 75 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 148 (accept_3_3 38 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 148
  (Polychromatic418967fa.accept_17_2_7_12_1_1078 36 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 75 148 (accept_3_3 35 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  75 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 75 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 148 (accept_3_3 32 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 75 148
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 75 148 (accept_3_3 29 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  75 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 75 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 148 (accept_3_3 26 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 75 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 75 148 (accept_3_3 23 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  75 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 75 148 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 148 (accept_3_3 20 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 75 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 75 148 (accept_3_3 17 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  75 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 75 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 148 (accept_3_3 14 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 148
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 148 (accept_3_3 11 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  75 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 75 148 (Polychromatic418967fa.accept_16_9_11_4_1_3194 9 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 148 (accept_3_3 8 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 75 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 148 (accept_3_3 5 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75
  148 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 75 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 75 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 148 (accept_3_3 2 75 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 75 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 148 (allA_of_3_1 74 74 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 148 (allA_succ_of_accept 72 73 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 148 (accept_3_3 71 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 148 (accept_3_3 68 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 66 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 148 (accept_3_3 65 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 148 (Polychromatic418967fa.accept_11_9_7_5_1_749 64 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 148 (accept_3_3 62 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 148
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 148 (accept_3_3 59 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 58 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 148 (accept_3_3 56 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 148 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 148 (accept_3_3 53 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 148 (accept_3_3 50 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 148 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 148 (accept_3_3 47 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 148 (accept_3_3 44 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 148
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 148 (accept_3_3 41 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 148 (accept_3_3 38 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 148
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 148 (accept_3_3 35 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 148 (accept_3_3 32 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 148 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 148 (accept_3_3 29 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 148 (Polychromatic418967fa.accept_16_12_9_4_1_4345 28 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 148 (accept_3_3 26 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 148
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 148 (accept_3_3 23 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 148 (accept_3_3 20 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 148
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 148 (accept_3_3 17 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 148 (accept_3_3 14 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 148 (accept_3_3 11 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 148 (accept_3_3 8 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 73 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 148
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 148 (accept_3_3 5 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  148 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 73 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 73 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 73 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 148 (accept_3_3 2 73 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 73 148 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 73 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 148 (allA_succ_of_accept 71
  72 148 (accept_3_3 71 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 72 148 2 35 36 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 72 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 72 148 4 17 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 72 148 (Polychromatic418967fa.accept_11_1_6_5_1_1732 67 72 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 148 2 33 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 148 (accept_3_3 65 72 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 148 4 16 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 148 (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 72 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 72 148 2 31 36 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 72 148
  (Polychromatic418967fa.accept_15_1_12_13_1_944 61 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 72 148 4 15 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 72 148 (accept_3_3 59 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72
  148 2 29 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  72 148 (Polychromatic418967fa.accept_14_1_2_8_1_655 57 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 72 148 4 14 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 72 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 72 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 148 2 27 36 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 148 (accept_3_3 53 72 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 148 4 13 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 72 148
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 51 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 72 148 2 25 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 72 148 (Polychromatic418967fa.accept_16_1_8_4_1_4334 49 72 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 148 4 12 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 148 (accept_3_3 47 72 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 148 2 23 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 72 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 72 148 4 11 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 72 148
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 72 148 2 21 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 72 148 (accept_3_3 41 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72
  148 4 10 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  72 148 (Polychromatic418967fa.accept_16_7_8_4_1_689 39 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 72 148 2 19 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 72 148 (Polychromatic418967fa.accept_13_11_7_5_1_2314 37 72 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 148 4 9 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 148 (accept_3_3 35 72 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 148 2 17 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 148 (Polychromatic418967fa.accept_15_3_12_13_1_2549
  33 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 148 4 8 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 72 148 2 15 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 72 148 (accept_3_3 29 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72
  148 4 7 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  72 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 72 148 2 13 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 72 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 72 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 148 4 6 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 148 (accept_3_3 23 72 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 148 2 11 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 148 (Polychromatic418967fa.accept_11_10_6_5_1_1239
  21 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 148 4 5 18 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 148
  (Polychromatic418967fa.accept_16_3_8_4_1_3279 19 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 148 2 9 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 148 (accept_3_3 17 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72
  148 4 4 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  72 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 72 148 2 7 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 72 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 72 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 148 4 3 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 148 (accept_3_3 11 72 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 148 2 5 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 72 148 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 72 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 148 4 2 18 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 148
  (Polychromatic418967fa.accept_16_7_8_4_1_689 7 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 72 148 2 3 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 72 148 (accept_3_3 5 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 148
  4 1 18 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72
  148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 72 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 148 2 1 36 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 148 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 72 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 72
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 148 (allA_of_3_1 71 71 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 148 (allA_succ_of_accept 69 70 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 69 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 70 148 2 34 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 70 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 67 70 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 148 2 33 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 148 (accept_3_3 65 70 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 148 2 32 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 148 (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 70
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 70 148 2 31 35 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 70 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 70 148 2 30 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 70 148 (accept_3_3 59 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70
  148 2 29 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57
  70 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 57 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 70 148 2 28 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 70 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 70 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 70 148 2 27 35 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 70 148 (accept_3_3 53 70 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70 148 2 26 35 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 70 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 51 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 70 148 2 25 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 70 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 70 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 148 2 24 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 148 (accept_3_3 47 70 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 148 2 23 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 148 (Polychromatic418967fa.accept_16_13_6_4_1_3277 45 70 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 70 148 2 22 35 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 70 148
  (Polychromatic418967fa.accept_11_10_4_5_1_359 43 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 70 148 2 21 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 70 148 (accept_3_3 41 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  148 2 20 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 70 148 2 19 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 70 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 70 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 70 148 2 18 35 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 70 148 (accept_3_3 35 70 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 70 148 2 17 35 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 70 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 70 148 2 16 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 70 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 70 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 148 2 15 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 148 (accept_3_3 29 70 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 148 2 14 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 148 (Polychromatic418967fa.accept_15_12_10_13_1_4497 27 70
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 70 148 2 13 35 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 70 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 70 148 2 12 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 70 148 (accept_3_3 23 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70
  148 2 11 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  70 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 70 148 2 10 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 70 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 70 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 70 148 2 9 35 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 70 148 (accept_3_3 17 70 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70 148 2 8 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 70 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 70 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 70 148 2 7 35 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 70 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 70 148 2 6 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 70 148 (accept_3_3 11 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  148 2 5 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 148 (Polychromatic418967fa.accept_19_9_13_15_1_3677 9 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 70 148 2 4 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 70 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 70 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 70 148 2 3 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 70 148 (accept_3_3 5 70 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 148 2 2 35 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 70 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 70 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 70 148 2 1 35 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 70 148
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 70 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 70 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 148
  (allA_succ_of_accept 68 69 148 (accept_3_3 68 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 66 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 148 (accept_3_3 65 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 148
  (Polychromatic418967fa.accept_11_8_3_5_1_355 63 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 148 (accept_3_3 62 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 148 (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 148 (accept_3_3 59 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 69 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 148
  (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 148 (accept_3_3 56 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 148 (accept_3_3 53 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 148 (accept_3_3 50 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 48 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 148 (accept_3_3 47 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 148
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 45 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 148 (accept_3_3 44 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 148 (accept_3_3 41 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 148 (accept_3_3 38 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 148 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 148 (accept_3_3 35 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 69 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 148 (accept_3_3 32 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 148 (accept_3_3 29 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 148
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 148 (accept_3_3 26 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 148 (accept_3_3 23 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 148 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 148 (accept_3_3 20 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 148 (accept_3_3 17 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 148
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 148 (accept_3_3 14 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 148 (accept_3_3 11 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 69 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 148 (accept_3_3 8 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 69 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 148 (accept_3_3 5 69 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 69 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  69 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 148 (accept_3_3 2 69 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 69
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 148 (allA_of_3_1 68 68 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 148 (allA_succ_of_accept 66 67 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 148 (accept_3_3 65 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 148 (Polychromatic418967fa.accept_13_12_2_5_1_1634 64 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 148 (accept_3_3 62 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 148
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 60 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 148 (accept_3_3 59 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 148 (accept_3_3 56 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 54 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 148 (accept_3_3 53 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 148 (accept_3_3 50 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 148 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 148
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 148 (accept_3_3 47 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 148 (accept_3_3 44 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 148 (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 148
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 148 (accept_3_3 41 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 148 (accept_3_3 38 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 148 (Polychromatic418967fa.accept_20_17_7_8_1_7919 37 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 148
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 148 (accept_3_3 35 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 148 (accept_3_3 32 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 148
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 148 (accept_3_3 29 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 148 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 148 (accept_3_3 26 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 148 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 148 (accept_3_3 23 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 148 (accept_3_3 20 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 148
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 148 (accept_3_3 17 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 148 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 148 (accept_3_3 14 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 148 (Polychromatic418967fa.accept_17_13_16_12_1_6562 13 67 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 148 (accept_3_3 11 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 148 (accept_3_3 8 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 148
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 148 (accept_3_3 5 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  148 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 67 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 148 (accept_3_3 2 67 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 148 (Polychromatic418967fa.accept_16_1_3_4_1_665 1 67 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 148 (allA_succ_of_accept 65 66
  148 (accept_3_3 65 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 148 2 32 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 66 148
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 66 148 2 31 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 66 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 66 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 148 2 30 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 148 (accept_3_3 59 66 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 148 2 29 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 66 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 66 148 2 28 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 66 148
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 66 148 2 27 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 66 148 (accept_3_3 53 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66
  148 2 26 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  66 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 66 148 2 25 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 66 148 (Polychromatic418967fa.accept_15_4_6_13_1_956 49 66 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 148 2 24 33 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 148 (accept_3_3 47 66 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 148 2 23 33 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 66 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 66 148 2 22 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 66 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 43 66 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 148 2 21 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 148 (accept_3_3 41 66 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 148 2 20 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 66 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 148 2 19 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 66 148 2 18 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 66 148 (accept_3_3 35 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66
  148 2 17 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  66 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 66 148 2 16 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 66 148 (Polychromatic418967fa.accept_17_14_15_12_1_1921 31 66 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 148 2 15 33 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 148 (accept_3_3 29 66 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 148 2 14 33 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 66 148
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 66 148 2 13 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 66 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 66 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 148 2 12 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 148 (accept_3_3 23 66 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 148 2 11 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 66 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 148 2 10 33 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 66 148 2 9 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 66 148 (accept_3_3 17 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66
  148 2 8 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  66 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 66 148 2 7 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 66 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 66 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 148 2 6 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 66 148 (accept_3_3 11 66 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 148 2 5 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 66 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 66 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 148 2 4 33 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 66 148 2 3 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 66 148 (accept_3_3 5 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 148
  2 2 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66
  148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 66 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 66 148 2 1 33 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 66 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 66 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 148 (allA_of_3_1 65 65 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 148 (allA_succ_of_accept 63 64 148
  (Polychromatic418967fa.accept_24_15_16_4_1_7918 63 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 64 148 2 31 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 64 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 61 64 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 148 4 15 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 148 (accept_3_3 59 64 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 148 2 29 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 64 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 64 148 4 14 16 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 64 148
  (Polychromatic418967fa.accept_15_10_4_13_1_4506 55 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 64 148 2 27 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 64 148 (accept_3_3 53 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64
  148 4 13 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  64 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 64 148 2 25 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 64 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 64 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 64 148 4 12 16 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 64 148 (accept_3_3 47 64 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64 148 2 23 32 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 64 148
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 64 148 4 11 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 64 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 64 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 148 2 21 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 148 (accept_3_3 41 64 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 148 4 10 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 64 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 148 2 19 32 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 148
  (Polychromatic418967fa.accept_19_18_7_15_1_3733 37 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 148 4 9 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 148 (accept_3_3 35 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  148 2 17 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 148 4 8 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 148 (Polychromatic418967fa.accept_18_13_10_4_1_5150 31 64 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 148 2 15 32 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 148 (accept_3_3 29 64 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 148 4 7 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 148 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  27 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 148 2 13 32 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 148
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 148 4 6 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 148 (accept_3_3 23 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  148 2 11 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 148 4 5 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 64 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 148 2 9 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 148 (accept_3_3 17 64 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 148 4 4 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 64 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 148 2 7 32 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 148
  (Polychromatic418967fa.accept_18_13_10_4_1_5150 13 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 148 4 3 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 148 (accept_3_3 11 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  148 2 5 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 148 4 2 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 64 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 148 2 3 32 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 148 (accept_3_3 5 64 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 148 4 1 16 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 64 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 148 2 1 32 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 148
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 64 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 148
  (allA_succ_of_accept 62 63 148 (accept_3_3 62 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 63 148 (Polychromatic418967fa.accept_16_12_15_4_1_5422 60 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 148 (accept_3_3 59 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 148 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 63 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 148
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 63 148 (accept_3_3 56 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 63 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 148 (accept_3_3 53 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 148 (Polychromatic418967fa.accept_22_8_19_16_1_6137 52 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 148
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 63 148 (accept_3_3 50 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 63 148 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 148 (accept_3_3 47 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 148
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 63 148 (accept_3_3 44 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 63 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 148 (accept_3_3 41 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 148 (Polychromatic418967fa.accept_15_10_3_13_1_4480 40 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 148
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 63 148 (accept_3_3 38 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 63 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 148 (accept_3_3 35 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 148 (Polychromatic418967fa.accept_14_6_7_8_1_624 34 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 148
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 63 148 (accept_3_3 32 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 63 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 148 (accept_3_3 29 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 148 (Polychromatic418967fa.accept_16_12_15_4_1_5422 28 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 148
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 63 148 (accept_3_3 26 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 63 148 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 148 (accept_3_3 23 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 148 (Polychromatic418967fa.accept_27_22_9_13_1_7917 22 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 148
  (Polychromatic418967fa.accept_10_1_3_8_1_136 21 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 63 148 (accept_3_3 20 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 63 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 148 (accept_3_3 17 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 148
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 148 (accept_3_3 14 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 148 (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 148 (accept_3_3 11 63 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 148 (Polychromatic418967fa.accept_15_10_3_13_1_4480 10 63
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 148
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 148 (accept_3_3 8 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 63 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 63 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 148 (accept_3_3 5 63 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 148 (Polychromatic418967fa.accept_19_4_6_15_1_7916 4 63 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 148 (accept_3_3 2 63 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 63
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 148 (allA_of_3_1 62 62 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 61 148 (allA_succ_of_accept 60 61 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 148 (accept_3_3 59 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 148 (accept_3_3 56 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 148
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 148 (accept_3_3 53 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 148 (accept_3_3 50 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 148 (accept_3_3 47 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 148 (accept_3_3 44 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 148 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 148 (accept_3_3 41 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 148 (Polychromatic418967fa.accept_13_1_9_5_1_1598 40 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 148 (accept_3_3 38 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 148
  (Polychromatic418967fa.accept_17_2_10_12_1_7915 36 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 148 (accept_3_3 35 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 148 (accept_3_3 32 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 148
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 148 (accept_3_3 29 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 148 (accept_3_3 26 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 148 (accept_3_3 23 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 148 (accept_3_3 20 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 148 (accept_3_3 17 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 148 (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 148 (accept_3_3 14 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 148
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 148 (accept_3_3 11 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 148 (accept_3_3 8 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 148 (Polychromatic418967fa.accept_16_7_13_4_1_1348 7 61 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 148 (accept_3_3 5 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  148 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 61 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 61 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 148 (accept_3_3 2 61 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 61 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 148 (allA_succ_of_accept 59 60 148 (accept_3_3 59 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 148 2 29 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 60 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 148 4 14 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 55
  60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 148 2 27 30 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 148 (accept_3_3 53
  60 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 148 4 13 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 148
  (Polychromatic418967fa.accept_13_12_8_5_1_976 51 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 148 2 25 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 148 (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 60 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60 148 4 12 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 60 148 (accept_3_3 47 60 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 148 2 23 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 60 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 60 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 148 4 11 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 148
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 60 148 2 21 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 60 148 (accept_3_3 41 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  148 4 10 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 60 148 2 19 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 60 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 148 4 9 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 148 (accept_3_3 35 60 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 148 2 17 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 60 148 4 8 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 60 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 60 148 2 15 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 60 148 (accept_3_3 29 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60
  148 4 7 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  60 148 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 60 148 2 13 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 60 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 60 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 148 4 6 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 148 (accept_3_3 23 60 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 148 2 11 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 148 4 5 15 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 60 148 2 9 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 60 148 (accept_3_3 17 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60
  148 4 4 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  60 148 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 60 148 2 7 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 60 148 (Polychromatic418967fa.accept_16_13_12_4_1_4323 13 60 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 148 4 3 15 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 148 (accept_3_3 11 60 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 148 2 5 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 148 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 60 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 148 4 2 15 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 148
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 148 2 3 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 148 (accept_3_3 5 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 148
  4 1 15 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60
  148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 60 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 148 2 1 30 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 60 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 60 148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 148 (allA_of_3_1 59 59 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 148
  (allA_succ_of_accept 57 58 148 (Polychromatic418967fa.accept_14_1_2_8_1_655 57 58 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 148 2 28 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 55
  58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 148 2 27 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 148 (accept_3_3 53
  58 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 148 2 26 29 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 148
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 148 2 25 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 58 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 58 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 148 2 24 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 148 (accept_3_3 47 58 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 148 2 23 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 58 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 148 2 22 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 148
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 148 2 21 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 58 148 (accept_3_3 41 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58
  148 2 20 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  58 148 (Polychromatic418967fa.accept_17_5_7_12_1_1951 39 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 148 2 19 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 58 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 148 2 18 29 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 148 (accept_3_3 35 58 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 148 2 17 29 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 148
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 33 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 148 2 16 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 58 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 148 2 15 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 148 (accept_3_3 29 58 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 148 2 14 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 58 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 148 2 13 29 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 148 2 12 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 148 (accept_3_3 23 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58
  148 2 11 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  58 148 (Polychromatic418967fa.accept_17_4_7_12_1_6556 21 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 148 2 10 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 58 148 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 58 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 148 2 9 29 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 148 (accept_3_3 17 58 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 148 2 8 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 148 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 58 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 148 2 7 29 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 13 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 148 2 6 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 148 (accept_3_3 11 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  148 2 5 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 148 (Polychromatic418967fa.accept_25_9_8_23_1_7913 9 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 148 2 4 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 58 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 148 2 3 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 148 (accept_3_3 5 58 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 148 2 2 29 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 58 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 148 2 1 29 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 58 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 148)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 148 (allA_succ_of_accept 56
  57 148 (accept_3_3 56 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 57 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 55 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 57 148 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 57 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 148 (accept_3_3 53 57 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 57 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 51
  57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 148 (accept_3_3 50 57
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 57 148
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 48 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 57 148 (accept_3_3 47 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  57 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 57 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 148 (accept_3_3 44 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 57 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 57 148 (accept_3_3 41 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  57 148 (Polychromatic418967fa.accept_15_10_12_13_1_2585 40 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 57 148 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 148 (accept_3_3 38 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 57 148
  (Polychromatic418967fa.accept_17_2_6_12_1_7912 36 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 57 148 (accept_3_3 35 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  57 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 57 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 148 (accept_3_3 32 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 57 148
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 57 148 (accept_3_3 29 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  57 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 57 148 (Polychromatic418967fa.accept_16_11_9_4_1_5438 27 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 148 (accept_3_3 26 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 57 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 57 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 57 148 (accept_3_3 23 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  57 148 (Polychromatic418967fa.accept_23_22_11_10_1_6063 22 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 57 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 148 (accept_3_3 20 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 57 148
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 57 148 (accept_3_3 17 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  57 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 57 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 148 (accept_3_3 14 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 57 148
  (Polychromatic418967fa.accept_16_12_9_4_1_4345 12 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 57 148 (accept_3_3 11 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  57 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 57 148 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 148 (accept_3_3 8 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 148 (accept_3_3 5 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57
  148 (Polychromatic418967fa.accept_25_4_7_23_1_7911 4 57 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 148 (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 148 (accept_3_3 2 57 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 57 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 148 (allA_of_3_1 56 56 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 148 (allA_succ_of_accept 54 55 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 148 (accept_3_3 53 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 148 (accept_3_3 50 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 148 (Polychromatic418967fa.accept_14_7_13_8_1_2067 49 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 148 (accept_3_3 47 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 148 (accept_3_3 44 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 148
  (Polychromatic418967fa.accept_9_6_1_4_1_474 42 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 148 (accept_3_3 41 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 148 (accept_3_3 38 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 148
  (Polychromatic418967fa.accept_17_2_4_12_1_6587 36 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 148 (accept_3_3 35 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 148 (accept_3_3 32 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 148 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 148 (accept_3_3 29 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 148 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 148 (accept_3_3 26 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 148
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 148 (accept_3_3 23 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 148 (accept_3_3 20 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 148
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 148 (accept_3_3 17 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 148 (accept_3_3 14 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 148 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 148 (accept_3_3 11 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 148 (accept_3_3 8 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 148
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 148 (accept_3_3 5 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  148 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 55 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 148 (accept_3_3 2 55 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 148 (Polychromatic418967fa.accept_13_1_3_5_1_140 1 55 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 148 (allA_succ_of_accept 53 54 148
  (accept_3_3 53 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 54 148 2 26 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 54 148
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 54 148 2 25 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 49 54 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 148 2 24 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 148 (accept_3_3 47 54 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 148 2 23 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 54 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 54 148 2 22 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 148
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 148 2 21 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 148 (accept_3_3 41 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54
  148 2 20 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  54 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 54 148 2 19 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 54 148 (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 54 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 148 2 18 27 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 148 (accept_3_3 35 54 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 54 148 2 17 27 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 54 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 54 148 2 16 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 54 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 148 2 15 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 148 (accept_3_3 29 54 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 148 2 14 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 54 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 54 148 2 13 27 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 148 2 12 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 148 (accept_3_3 23 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54
  148 2 11 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  54 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 54 148 2 10 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 54 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 54 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 148 2 9 27 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 148 (accept_3_3 17 54 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 148 2 8 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 148 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 54 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 54 148 2 7 27 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 54 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 54 148 2 6 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 54 148 (accept_3_3 11 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54
  148 2 5 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  54 148 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 54 148 2 4 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 54 148 (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 54 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 148 2 3 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 54 148 (accept_3_3 5 54 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 148 2 2 27 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 54 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 54 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 54 148 2 1 27 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 148
  (Polychromatic418967fa.accept_19_1_16_15_1_2536 1 54 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 54 148)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 148 (allA_of_3_1 53 53 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 52 148 (allA_succ_of_accept 51 52 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 52 148 2 25 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 52 148 (Polychromatic418967fa.accept_17_15_1_12_1_7910 49 52 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 148 4 12 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 148 (accept_3_3 47 52 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 148 2 23 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 52 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 52 148 4 11 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 52 148
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 43 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 52 148 2 21 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 52 148 (accept_3_3 41 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52
  148 4 10 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  52 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 52 148 2 19 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 52 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 52 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 52 148 4 9 13 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 52 148 (accept_3_3 35 52 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52 148 2 17 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 52 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 33
  52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 52 148 4 8 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 52 148
  (Polychromatic418967fa.accept_22_9_8_16_1_7909 31 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 52 148 2 15 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 52 148 (accept_3_3 29 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52
  148 4 7 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  52 148 (Polychromatic418967fa.accept_23_4_6_10_1_7908 27 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 52 148 2 13 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 52 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 52 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 52 148 4 6 13 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 52 148 (accept_3_3 23 52 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52 148 2 11 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 52 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 21
  52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 52 148 4 5 13 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 52 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 52 148 2 9 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 52 148 (accept_3_3 17 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52
  148 4 4 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  52 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 52 148 2 7 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 52 148 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 52 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 52 148 4 3 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 52 148 (accept_3_3 11 52 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52 148 2 5 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 52 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 52 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 52 148 4 2 13 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 52 148
  (Polychromatic418967fa.accept_18_7_16_4_1_1674 7 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 52 148 2 3 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 52 148 (accept_3_3 5 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 148
  4 1 13 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 52
  148 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 52 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 52 148 2 1 26 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 52 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 52 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 52 148)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 148
  (allA_succ_of_accept 50 51 148 (accept_3_3 50 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 148 (accept_3_3 47 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 148 (accept_3_3 44 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 148 (Polychromatic418967fa.accept_11_9_7_5_1_749 42 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 148 (accept_3_3 41 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 148 (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 148
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 148 (accept_3_3 38 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 148 (Polychromatic418967fa.accept_19_17_13_15_1_1402 36 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 148 (accept_3_3 35 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 51 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 148
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 148 (accept_3_3 32 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 30 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 148 (accept_3_3 29 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 148 (accept_3_3 26 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 148 (accept_3_3 23 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 148 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 148 (accept_3_3 20 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 148 (accept_3_3 17 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 148
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 148 (accept_3_3 14 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 148 (accept_3_3 11 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 51 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 148
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 148 (accept_3_3 8 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 51 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 148 (accept_3_3 5 51 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 148 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 51 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  51 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 148 (accept_3_3 2 51 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 51
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  148))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 148 (allA_of_3_1 50 50 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 148 (allA_succ_of_accept 48 49 148 (Polychromatic418967fa.accept_14_6_7_8_1_624 48
  49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 148 (accept_3_3 47 49
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 148
  (Polychromatic418967fa.accept_12_10_1_4_1_392 46 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 49 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 148 (accept_3_3 44 49 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 49 148 (Polychromatic418967fa.accept_13_4_10_5_1_1644 43 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 148
  (Polychromatic418967fa.accept_19_4_11_15_1_3743 42 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 148 (accept_3_3 41 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 148 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 148 (accept_3_3 38 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 148
  (Polychromatic418967fa.accept_15_6_4_13_1_403 36 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 148 (accept_3_3 35 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 148 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 148 (accept_3_3 32 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 148 (Polychromatic418967fa.accept_10_1_9_8_1_123 31 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 148
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 148 (accept_3_3 29 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 148 (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 148 (accept_3_3 26 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 148 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 148
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 148 (accept_3_3 23 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 148 (accept_3_3 20 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 148 (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 148
  (Polychromatic418967fa.accept_17_1_15_12_1_7907 18 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 148 (accept_3_3 17 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 148 (Polychromatic418967fa.accept_19_16_11_15_1_7906 16 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 148 (accept_3_3 14 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 148
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 148 (accept_3_3 11 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 148 (accept_3_3 8 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 148 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 49 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 148
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 148 (accept_3_3 5 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 49 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 49 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 49 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 148 (accept_3_3 2 49 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 49 148 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 49 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 148))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  48 148 (allA_succ_of_accept 47 48 148 (accept_3_3 47 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  46 48 148 2 23 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 148 (Polychromatic418967fa.accept_17_11_14_12_1_2995 45 48 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 148 4 11 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 43
  48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 148 2 21 24 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 148 (accept_3_3 41
  48 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 148 4 10 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 148
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 148 2 19 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 48 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 148 4 9 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 148 (accept_3_3 35 48 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 48 148 2 17 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 48 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 48 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 148 4 8 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 148
  (Polychromatic418967fa.accept_15_1_3_13_1_2548 31 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 48 148 2 15 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 48 148 (accept_3_3 29 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48
  148 4 7 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  48 148 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 48 148 2 13 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 48 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 48 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48 148 4 6 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 48 148 (accept_3_3 23 48 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 148 2 11 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 48 148 (Polychromatic418967fa.accept_11_10_4_5_1_359
  21 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 148 4 5 12 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 48 148 2 9 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 48 148 (accept_3_3 17 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48
  148 4 4 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  48 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 48 148 2 7 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 48 148 (Polychromatic418967fa.accept_28_13_20_8_1_7905 13 48 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 148 4 3 12 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 148 (accept_3_3 11 48 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 148 2 5 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 48 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 48 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 148 4 2 12 37 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 148
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 148 2 3 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 148 (accept_3_3 5 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 148
  4 1 12 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48
  148 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 48 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 48 148 2 1 24 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 48 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 48 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 148)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 148 (allA_of_3_1 47 47 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 148 (allA_succ_of_accept 45 46
  148 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 46 148 2 22 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 46 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 46 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 148 2 21 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 148 (accept_3_3 41 46 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 148 2 20 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 46 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 46 148 2 19 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 46 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 46 148 2 18 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 46 148 (accept_3_3 35 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46
  148 2 17 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  46 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 46 148 2 16 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 46 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 46 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 46 148 2 15 23 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 46 148 (accept_3_3 29 46 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46 148 2 14 23 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 46 148
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 46 148 2 13 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 46 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 46 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 148 2 12 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 148 (accept_3_3 23 46 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 148 2 11 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 46 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 46 148 2 10 23 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 46 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 46 148 2 9 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 46 148 (accept_3_3 17 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 46
  148 2 8 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  46 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 46 148 2 7 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 46 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 46 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 148 2 6 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 148 (accept_3_3 11 46 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 148 2 5 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 46 148 (Polychromatic418967fa.accept_16_9_14_4_1_3225 9 46 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 46 148 2 4 23 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 46 148
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 46 148 2 3 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 46 148 (accept_3_3 5 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 46 148
  2 2 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 46
  148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 46 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 46 148 2 1 23 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 46 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 46 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 46 148)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 148
  (allA_succ_of_accept 44 45 148 (accept_3_3 44 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 45 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 148 (accept_3_3 41 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 45 148
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 45 148 (accept_3_3 38 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 45 148 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 148 (accept_3_3 35 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 148 (Polychromatic418967fa.accept_20_14_5_8_1_4870 34 45
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 45 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 45 148 (accept_3_3 32 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 45 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 148 (accept_3_3 29 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 148 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 148
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 148 (accept_3_3 26 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 45 148 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 148 (accept_3_3 23 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 45 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 148
  (Polychromatic418967fa.accept_22_21_1_16_1_7904 21 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 45 148 (accept_3_3 20 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 45 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 148 (accept_3_3 17 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 148
  (Polychromatic418967fa.accept_18_15_9_4_1_5185 15 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 45 148 (accept_3_3 14 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 45 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 148 (accept_3_3 11 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 148 (Polychromatic418967fa.accept_13_10_6_5_1_2297 10 45 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 148 (accept_3_3 8 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 45 148 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 45 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 148 (accept_3_3 5 45 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 45 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 45 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 148 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3
  45 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 148 (accept_3_3 2 45 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 45
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  148))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 148 (allA_of_3_1 44 44 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 43 148 (allA_succ_of_accept 42 43 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 42 43 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 43 148 (accept_3_3 41 43 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 43 148 (Polychromatic418967fa.accept_13_1_4_5_1_113
  40 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 43 148 (accept_3_3 38 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  43 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 43 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 43 148 (accept_3_3 35 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 43 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 43 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 43 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 43 148 (accept_3_3 32 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  43 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 43 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 30 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 43 148 (accept_3_3 29 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 43 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 43 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 43 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 43 148 (accept_3_3 26 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  43 148 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 43 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 24 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 43 148 (accept_3_3 23 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 43 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 43 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 43 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 43 148 (accept_3_3 20 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  43 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 43 148 (Polychromatic418967fa.accept_20_18_3_8_1_7903 18 43 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 43 148 (accept_3_3 17 43 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 43 148 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 43 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 43 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 43 148 (accept_3_3 14 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  43 148 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 43 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 43 148 (accept_3_3 11 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 43 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 43 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 43 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 43 148 (accept_3_3 8 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 43
  148 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 43 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 43 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 43 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 43 148 (accept_3_3 5 43 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 43 148 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 43 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 43 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 43
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 148 (accept_3_3 2 43 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 43
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43
  148))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 148 (allA_succ_of_accept 41 42 148 (accept_3_3 41 42 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 148 2 20 21 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 148 2 19 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 42 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 148 2 18 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 148 (accept_3_3 35 42 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 148 2 17 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 148 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 42 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 148 2 16 21 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 148
  (Polychromatic418967fa.accept_15_1_12_13_1_944 31 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 42 148 2 15 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 42 148 (accept_3_3 29 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 42
  148 2 14 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  42 148 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 42 148 2 13 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 42 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 42 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 148 2 12 21 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 148 (accept_3_3 23 42 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 148 2 11 21 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 42 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 42 148 2 10 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 42 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 42 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 148 2 9 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 42 148 (accept_3_3 17 42 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 42 148 2 8 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 42 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 42 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 42 148 2 7 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 148 (Polychromatic418967fa.accept_19_13_4_15_1_7902
  13 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 148 2 6 21 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 148 (accept_3_3 11
  42 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 42 148 2 5 21 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 42 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 42 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 42 148 2 4 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 42 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 148 2 3 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 148 (accept_3_3 5 42 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 42 148 2 2 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 42 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 42 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 42 148 2 1 21 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 42
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  148)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 148 (allA_of_3_1 41 41 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 40 148 (allA_succ_of_accept 39 40 148 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 40 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 40 148 2 19 20 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 40 148
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 37 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 40 148 4 9 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 40 148 (accept_3_3 35 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 40
  148 2 17 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  40 148 (Polychromatic418967fa.accept_15_3_10_13_1_2605 33 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 40 148 4 8 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 40 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 40 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 40 148 2 15 20 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 40 148 (accept_3_3 29 40 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40 148 4 7 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 40 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 40 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 40 148 2 13 20 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 40 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 40 148 4 6 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 40 148 (accept_3_3 23 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40
  148 2 11 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  40 148 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 40 148 4 5 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 40 148 (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 40 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 40 148 2 9 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 40 148 (accept_3_3 17 40 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40 148 4 4 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 40 148 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 40 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 40 148 2 7 20 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 40 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 40 148 4 3 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 40 148 (accept_3_3 11 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  148 2 5 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  40 148 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 40 148 4 2 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 40 148 (Polychromatic418967fa.accept_16_7_8_4_1_689 7 40 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 40 148 2 3 20 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 40 148 (accept_3_3 5 40 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 148 4 1 10 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 40 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 40 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 40 148 2 1 20 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 40 148
  (Polychromatic418967fa.accept_15_1_10_13_1_939 1 40 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 40 148)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 148 (allA_succ_of_accept 38 39 148 (accept_3_3
  38 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 148 (Polychromatic418967fa.accept_19_17_1_15_1_7901 36 39 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 148 (accept_3_3 35 39 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 33
  39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 148 (accept_3_3 32 39
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 148 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 39 148
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 39 148 (accept_3_3 29 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  39 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 39 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 148 (accept_3_3 26 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 39 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 39 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 39 148 (accept_3_3 23 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  39 148 (Polychromatic418967fa.accept_15_7_9_13_1_3451 22 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 39 148 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 148 (accept_3_3 20 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 39 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 39 148
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 39 148 (accept_3_3 17 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  39 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 39 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 148 (accept_3_3 14 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 39 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 39 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 39 148 (accept_3_3 11 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  39 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 39 148 (Polychromatic418967fa.accept_17_9_5_12_1_6606 9 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 148 (accept_3_3 8 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 39 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 148 (accept_3_3 5 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  148 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 39 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 39 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 148 (accept_3_3 2 39 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 39 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 148))))))))))))))))))))))))))))))))))))))) (allB_succ 38 148
  (allA_of_3_1 38 38 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 148 (allA_succ_of_accept 36 37 148
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 148 (accept_3_3 35 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 148 (accept_3_3 32 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 37 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 30 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 148 (accept_3_3 29 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 148 (Polychromatic418967fa.accept_16_12_5_4_1_3275 28 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 148 (accept_3_3 26 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 37 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 148 (accept_3_3 23 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 148 (accept_3_3 20 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 148 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 37 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 148
  (Polychromatic418967fa.accept_23_18_14_10_1_7900 18 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 37 148 (accept_3_3 17 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 37 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 37 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 37 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 148 (accept_3_3 14 37 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 148 (accept_3_3 11 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 148 (accept_3_3 8 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 37 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 148 (accept_3_3 5 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  148 (Polychromatic418967fa.accept_19_4_18_15_1_7899 4 37 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 148 (accept_3_3 2 37 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 37 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 148))))))))))))))))))))))))))))))))))))) (allB_succ
  36 148 (allA_succ_of_accept 35 36 148 (accept_3_3 35 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd
  34 36 148 2 17 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 36 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 148 4 8 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 148 (Polychromatic418967fa.accept_19_12_17_15_1_6460 31 36
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 148 2 15 18 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 148 (accept_3_3 29
  36 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 148 4 7 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 148
  (Polychromatic418967fa.accept_17_10_2_12_1_1070 27 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 148 2 13 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 148 (Polychromatic418967fa.accept_22_3_14_16_1_6181 25 36 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 148 4 6 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 148 (accept_3_3 23 36 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 148 2 11 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 148 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 36 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 148 4 5 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 148
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 36 148 2 9 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 36 148 (accept_3_3 17 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36
  148 4 4 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  36 148 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 36 148 2 7 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 36 148 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 36 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36 148 4 3 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 36 148 (accept_3_3 11 36 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 148 2 5 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 36 148 (Polychromatic418967fa.accept_23_9_13_10_1_7898 9 36 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 148 4 2 9 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 148
  (Polychromatic418967fa.accept_15_7_6_13_1_936 7 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 36 148 2 3 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 36 148 (accept_3_3 5 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 148
  4 1 9 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 148
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 36 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 148 2 1 18 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 148 (Polychromatic418967fa.accept_19_1_17_15_1_7897 1 36 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 148)))))))))))))))))))))))))))))))))))) (allB_succ 35 148 (allA_of_3_1 35
  35 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 148 (allA_succ_of_accept 33 34 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 148 2 16 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 31 34 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 148 2 15 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 148 (accept_3_3 29 34 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 148 2 14 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 148 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 34 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 148 2 13 17 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 148 2 12 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 148 (accept_3_3 23 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  148 2 11 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 148 2 10 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 34 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 148 2 9 17 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 148 (accept_3_3 17 34 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 148 2 8 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 34 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 148 2 7 17 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 148 2 6 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 148 (accept_3_3 11 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  148 2 5 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 148 2 4 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 34 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 148 2 3 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 148 (accept_3_3 5 34 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 148 2 2 17 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 148 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 34 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 148 2 1 17 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 148
  (Polychromatic418967fa.accept_9_1_7_4_1_52 1 34 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 148)))))))))))))))))))))))))))))))))) (allB_succ 33 148 (allA_succ_of_accept 32 33 148 (accept_3_3 32 33
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 33 148 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 33 148 (accept_3_3 29 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  33 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 33 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 148 (accept_3_3 26 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 33 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 33 148
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 33 148 (accept_3_3 23 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  33 148 (Polychromatic418967fa.accept_25_22_8_23_1_7896 22 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 33 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 148 (accept_3_3 20 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 33 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 33 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 33 148 (accept_3_3 17 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  33 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 33 148 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 148 (accept_3_3 14 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 33 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 33 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 33 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 33 148 (accept_3_3 11 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  33 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 33 148 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 148 (accept_3_3 8 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 33 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 148 (accept_3_3 5 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33
  148 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 33 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 33 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 33 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 148 (accept_3_3 2 33 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 33 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 33 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 148))))))))))))))))))))))))))))))))) (allB_succ 32 148
  (allA_of_3_1 32 32 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 31 148 (allA_succ_of_accept 30 31 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 148 (accept_3_3 29 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 148 (Polychromatic418967fa.accept_16_12_15_4_1_5422 28 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 148 (accept_3_3 26 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 148 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 31 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 148
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 148 (accept_3_3 23 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 148 (accept_3_3 20 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 31 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 148
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 31 148 (accept_3_3 17 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  31 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 31 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 148 (accept_3_3 14 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 148 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 31 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 148
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 148 (accept_3_3 11 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 148 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 148 (accept_3_3 8 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 148 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 31 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 148
  (Polychromatic418967fa.accept_19_6_12_15_1_7895 6 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 148 (accept_3_3 5 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  148 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 31 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 31 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 148 (accept_3_3 2 31 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 148 (Polychromatic418967fa.accept_20_1_11_8_1_7894 1 31 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 148))))))))))))))))))))))))))))))) (allB_succ 30 148
  (allA_succ_of_accept 29 30 148 (accept_3_3 29 30 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30
  148 2 14 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  30 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 30 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 30 148 2 13 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 30 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 30 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 148 2 12 15 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 148 (accept_3_3 23 30 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 148 2 11 15 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 30 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 148 2 10 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 30 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 148 2 9 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 148 (accept_3_3 17 30 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 148 2 8 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 30 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 148 2 7 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  30 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 148 2 6 15 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 30 148 (accept_3_3 11
  30 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 148 2 5 15 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 148
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 30 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 148 2 4 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 30 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 148 2 3 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 148 (accept_3_3 5 30 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 30 148 2 2 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 30 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 30 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 148 2 1 15 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 30
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 148))))))))))))))))))))))))))))))
  (allB_succ 29 148 (allA_of_3_1 29 29 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 148
  (allA_succ_of_accept 27 28 148 (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 28 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 28 148 2 13 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 28 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 25
  28 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 148 4 6 7 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 148 (accept_3_3 23
  28 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 28 148 2 11 14 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 28 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 28 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 28 148 4 5 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 28 148 (Polychromatic418967fa.accept_16_3_12_4_1_170 19 28 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 28 148 2 9 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 28 148 (accept_3_3 17 28 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 28 148 4 4 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 28 148 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 28 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 28 148 2 7 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 28 148 (Polychromatic418967fa.accept_16_13_12_4_1_4323
  13 28 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 148 4 3 7 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 148 (accept_3_3 11
  28 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 148 2 5 14 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 148
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 28 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 28 148 4 2 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 28 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 28 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 28 148 2 3 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 28 148 (accept_3_3 5 28 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 28 148 4 1 7 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 28 148 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 28 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 28 148 2 1 14 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 28 148 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1
  28 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 148))))))))))))))))))))))))))))
  (allB_succ 27 148 (allA_succ_of_accept 26 27 148 (accept_3_3 26 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 27 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 27 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 148 (Polychromatic418967fa.accept_16_8_11_4_1_3290 24 27
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 148 (accept_3_3 23 27 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 148 (Polychromatic418967fa.accept_13_9_1_5_1_964
  22 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 148
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 148 (accept_3_3 20 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 27 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 148 (accept_3_3 17 27 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 148 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 27 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 148
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 148 (accept_3_3 14 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 148 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 27 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 148 (accept_3_3 11 27 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 148 (Polychromatic418967fa.accept_15_10_12_13_1_2585 10 27 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 148
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 148 (accept_3_3 8 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 27 148 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 27 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 148 (accept_3_3 5 27 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 27 148 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 27 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 148 (Polychromatic418967fa.accept_13_3_1_5_1_499 3
  27 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 148 (accept_3_3 2 27 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 27
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27 148)))))))))))))))))))))))))))
  (allB_succ 26 148 (allA_of_3_1 26 26 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 25 148
  (allA_succ_of_accept 24 25 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 25 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 148 (accept_3_3 23 25 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 25 148 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 25 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 148 (accept_3_3 20 25
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 148
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 25 148 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 25 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 148 (accept_3_3 17 25 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 25 148 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 25 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 25 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 25 148 (accept_3_3 14 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  25 148 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 25 148 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 25 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 148 (accept_3_3 11 25 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 25 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 25 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 25 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 25 148 (accept_3_3 8 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 25
  148 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 25 148 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 25 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 25 148 (accept_3_3 5 25 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 25 148 (Polychromatic418967fa.accept_13_4_12_5_1_476 4 25 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 148
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 25 148 (accept_3_3 2 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25
  148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 25 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 25 148))))))))))))))))))))))))) (allB_succ 24 148 (allA_succ_of_accept 23 24 148 (accept_3_3 23 24 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 148 2 11 12 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 24 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 148 4 5 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 148 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 24 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 148 2 9 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 148 (accept_3_3 17 24 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 148 4 4 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 148 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 24 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 148 2 7 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 148 (Polychromatic418967fa.accept_16_13_8_4_1_3250
  13 24 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 148 4 3 6 37 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 148 (accept_3_3 11
  24 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 148 2 5 12 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 148
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 24 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 148 4 2 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 148 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 24 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 148 2 3 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24 148 (accept_3_3 5 24 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 24 148 4 1 6 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 24 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 24 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 148 2 1 12 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 24
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 148)))))))))))))))))))))))) (allB_succ
  23 148 (allA_of_3_1 23 23 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 148 (allA_succ_of_accept 21 22
  148 (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 22 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 22 148 2 10 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 22 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 22 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 148 2 9 11 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 148 (accept_3_3 17 22 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 22 148 2 8 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 22 148 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 22 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 148 2 7 11 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 22 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 22 148 2 6 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 22 148 (accept_3_3 11 22 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22
  148 2 5 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  22 148 (Polychromatic418967fa.accept_15_9_7_13_1_1664 9 22 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 22 148 2 4 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 22 148 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 22 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 148 2 3 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 148 (accept_3_3 5 22 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 22 148 2 2 11 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 22 148 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 22 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 148 2 1 11 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 148
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 22 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 22 148)))))))))))))))))))))) (allB_succ 21 148 (allA_succ_of_accept 20 21 148 (accept_3_3 20 21 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 21 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 148
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 148 (accept_3_3 17 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  21 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 148 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 21 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 148 (accept_3_3 14 21 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 21 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 148
  (Polychromatic418967fa.accept_13_12_8_5_1_976 12 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 148 (accept_3_3 11 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  21 148 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 148 (accept_3_3 8 21 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 21 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 148
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 148 (accept_3_3 5 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21
  148 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 21 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 148 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 21 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 148 (accept_3_3 2 21 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 21 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 148))))))))))))))))))))) (allB_succ 20 148
  (allA_of_3_1 20 20 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 148 (allA_succ_of_accept 18 19 148
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 148 (accept_3_3 17 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 148 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 19 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 148 (accept_3_3 14 19 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 148 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 19 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 148 (accept_3_3 11 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 19 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 148 (accept_3_3 8 19 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 148 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 19 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 148
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 148 (accept_3_3 5 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  148 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 19 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 19 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 148 (accept_3_3 2 19 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 148 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 19 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 148))))))))))))))))))) (allB_succ 18 148 (allA_succ_of_accept 17
  18 148 (accept_3_3 17 18 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 148 2 8 9 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 148
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 18 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 148 2 7 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 148 (Polychromatic418967fa.accept_17_13_1_12_1_7893 13 18 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 148 2 6 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 148 (accept_3_3 11 18 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 148 2 5 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 148 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 18 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 148 2 4 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 148 (Polychromatic418967fa.accept_19_7_18_15_1_5061
  7 18 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 148 2 3 9 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 148 (accept_3_3 5 18
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 148 2 2 9 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 148
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 18 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 148 2 1 9 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 148 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 18 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 18 148)))))))))))))))))) (allB_succ 17 148 (allA_of_3_1 17 17 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 16 148 (allA_succ_of_accept 15 16 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 15 16 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 16 148 2 7 8 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 16 148 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 16 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 148 4 3 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 148 (accept_3_3 11 16 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 16 148 2 5 8 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 16 148 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9 16 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 148 4 2 4 37 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 148 (Polychromatic418967fa.accept_18_7_16_4_1_1674 7
  16 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 16 148 2 3 8 74 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 16 148 (accept_3_3 5 16
  148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 148 4 1 4 37 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 148
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 16 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 148 2 1 8 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 16 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 148)))))))))))))))) (allB_succ 15 148 (allA_succ_of_accept 14 15 148
  (accept_3_3 14 15 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 148
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 15 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 148 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 15 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 148 (accept_3_3 11 15 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 15 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 15 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 148 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9
  15 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 148 (accept_3_3 8 15 148
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 15
  148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 148
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 15 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 148 (accept_3_3 5 15 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15
  148 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 15 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 148 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 148 (accept_3_3 2 15 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 15 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 148))))))))))))))) (allB_succ 14 148 (allA_of_3_1 14
  14 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 148 (allA_succ_of_accept 12 13 148
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 13 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 148 (accept_3_3 11 13 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 148 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 13 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 13 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 148 (accept_3_3 8 13 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 148 (Polychromatic418967fa.accept_14_7_13_8_1_2067 7 13 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 148
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 13 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 148 (accept_3_3 5 13 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  148 (Polychromatic418967fa.accept_19_4_13_15_1_3676 4 13 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 13 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 148 (accept_3_3 2 13 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 148 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 13 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 148))))))))))))) (allB_succ 12 148
  (allA_succ_of_accept 11 12 148 (accept_3_3 11 12 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12
  148 2 5 6 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 12
  148 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 12 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 12 148 4 2 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 12 148 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 12 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 148 2 3 6 74 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 148 (accept_3_3 5 12 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 148 4 1 3 37 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 12 148 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 12 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 148 2 1 6 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 148
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 12 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 12 148)))))))))))) (allB_succ 11 148 (allA_of_3_1 11 11 148 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 10 148 (allA_succ_of_accept 9 10 148 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 10 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 148 2 4 5 74 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 148
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 10 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 148 2 3 5 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 148 (accept_3_3 5 10 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 148
  2 2 5 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 148
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 10 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 148 2 1 5 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 148 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 10 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 148)))))))))) (allB_succ 9 148 (allA_succ_of_accept 8 9 148 (accept_3_3 8
  9 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 148 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 9 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 148
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 9 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 9 148 (accept_3_3 5 9 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 148
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 9 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 9 148 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 9 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 148 (accept_3_3 2 9 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 9 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 9 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 148))))))))) (allB_succ 8 148 (allA_of_3_1 8 8 148 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 7 148 (allA_succ_of_accept 6 7 148
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 7 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 148 (accept_3_3 5 7 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 148
  (Polychromatic418967fa.accept_17_4_7_12_1_6556 4 7 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 148 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 7 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 148 (accept_3_3 2 7 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 148 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 7 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 148))))))) (allB_succ 6 148 (allA_succ_of_accept 5 6 148
  (accept_3_3 5 6 148 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 148 2 2 3 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 148
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 6 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 148 2 1 3 74 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 148 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 6 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 148)))))) (allB_succ 5 148 (allA_of_3_1 5 5 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 4 148 (allA_succ_of_accept 3 4 148 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 4 148
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 4 148 2 1 2 74 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 4 148
  (Polychromatic418967fa.accept_13_1_4_5_1_113 1 4 148 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 148)))) (allB_succ 3 148 (allA_succ_of_accept 2 3 148 (accept_3_3 2 3 148 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 148 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 3 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 148))) (allB_succ 2 148 (allA_of_3_1 2 2 148 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  148))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


