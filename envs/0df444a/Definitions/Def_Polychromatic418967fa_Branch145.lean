-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch145
-- name    : Polychromatic418967fa_Branch145
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:59.575169+00:00
-- url     : https://prove2.me/theorems/1dddc8ca-9ed6-432e-b3c2-2f910bd100cf
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

def Polychromatic418967fa.branch_145 : allB 145 145 :=
  allB_succ' 2 144 145 (Eq.refl Bool.true) (allA_succ_of_accept 1 144 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1
  144 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 145)) (allB_succ' 3 143 145
  (Eq.refl Bool.true) (allA_of_3_1 3 143 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 142 145 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 145 (accept_3_3 2 142 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 142 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 145)))) (allB_succ' 5 141 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 141 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 145 (accept_3_3 2 141 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 145 (Polychromatic418967fa.accept_15_1_6_10_1_23 1
  141 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 145))))) (allB_succ' 6 140 145
  (Eq.refl Bool.true) (allA_of_3_1 6 140 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 139 145 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 139 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 145 (accept_3_3 5 139 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 139 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 139 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 145 (accept_3_3 2 139 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 139 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 145))))))) (allB_succ' 8 138 145 (Eq.refl Bool.true) (allA_succ_of_accept 7 138 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 138 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 138 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 145 (accept_3_3 5 138 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 138 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 138 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  138 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 145 (accept_3_3 2 138
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 145
  (Polychromatic418967fa.accept_19_1_5_12_1_6249 1 138 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 145)))))))) (allB_succ' 9 137 145 (Eq.refl Bool.true) (allA_of_3_1 9 137 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 136 145 (Eq.refl Bool.true) (allA_succ_of_accept 9 136 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 145 (accept_3_3 8 136 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 145 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 136 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 145 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 136 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 145 (accept_3_3 5 136 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 145 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 136 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 145 (accept_3_3 2 136 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 136 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 145)))))))))) (allB_succ' 11 135 145 (Eq.refl Bool.true) (allA_succ_of_gcd 10 135 145 5 2 27
  29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 135 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 145 (accept_3_3 8 135 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 145 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 135 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 145 5 1 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  135 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 145 (accept_3_3 2 135 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 145 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 135 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 145))))))))))) (allB_succ' 12 134 145 (Eq.refl Bool.true) (allA_of_3_1 12 134 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 133 145 (Eq.refl Bool.true) (allA_succ_of_accept 12 133 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 145 (accept_3_3 11 133 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 145 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 133 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 145 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 133 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 145 (accept_3_3 8 133 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 133 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 145 (accept_3_3 5 133 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 133 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 133 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 145 (accept_3_3 2 133 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 145 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 133 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 145))))))))))))) (allB_succ' 14 132 145 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 132 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 132 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  132 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 145 (accept_3_3 11
  132 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 145
  (Polychromatic418967fa.accept_17_10_13_9_1_3913 10 132 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 145 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 132 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 145 (accept_3_3 8 132 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 132 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 145 (accept_3_3 5 132 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 132 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 145 (accept_3_3 2 132 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 132 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 145)))))))))))))) (allB_succ' 15 131 145 (Eq.refl
  Bool.true) (allA_of_3_1 15 131 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 130 145 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 130 145 5 3 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 130 145 (accept_3_3 14 130 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 130 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 130 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 145 (accept_3_3 11 130 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 145 5 2 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 145 (accept_3_3 8 130 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  130 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 130 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 130 145 5 1 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 130 145 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 130 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 145 (accept_3_3 2 130 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1
  130 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 145)))))))))))))))) (allB_succ' 17
  129 145 (Eq.refl Bool.true) (allA_succ_of_accept 16 129 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 145 (accept_3_3 14 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 145 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 129 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 145 (accept_3_3 11 129 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 145 (accept_3_3 8 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 145 (accept_3_3 5 129 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 145
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 145 (accept_3_3 2 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 129 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 145))))))))))))))))) (allB_succ' 18 128 145 (Eq.refl Bool.true) (allA_of_3_1 18 128 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 127 145 (Eq.refl Bool.true) (allA_succ_of_accept 18 127 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 145 (accept_3_3 17 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 145 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 145 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 127 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 145 (accept_3_3 14 127 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 127 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 145
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 145 (accept_3_3 11 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 145 (Polychromatic418967fa.accept_20_9_7_5_1_2114 9 127 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 145 (accept_3_3 8 127 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 145 (Polychromatic418967fa.accept_21_7_1_19_1_6021 7 127 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 145 (accept_3_3 5 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 127 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 127 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 145 (accept_3_3 2 127 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 127 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 145))))))))))))))))))) (allB_succ' 20 126 145
  (Eq.refl Bool.true) (allA_succ_of_accept 19 126 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 145
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 126 145 (accept_3_3 17 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 126 145 (Polychromatic418967fa.accept_13_3_9_2_1_1486 16 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 126 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 145 (accept_3_3 14 126 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 145 (Polychromatic418967fa.accept_16_13_14_1_1_2094 13 126 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 145
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 145 (accept_3_3 11 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 145 (Polychromatic418967fa.accept_20_10_6_5_1_7776 10 126 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 126 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 145 (accept_3_3 8 126 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  126 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 145
  (Polychromatic418967fa.accept_13_6_9_2_1_838 6 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 126 145 (accept_3_3 5 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  126 145 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 126 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 126 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 145 (accept_3_3 2 126 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 145 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 126 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 145)))))))))))))))))))) (allB_succ' 21 125 145
  (Eq.refl Bool.true) (allA_of_3_1 21 125 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 124 145 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 145 (accept_3_3 20 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 145 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 124 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 145
  (Polychromatic418967fa.accept_13_5_7_2_1_852 18 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 145 (accept_3_3 17 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 145 (accept_3_3 14 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 124 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 145 (accept_3_3 11 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 145 (accept_3_3 8 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 145 (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 124 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 145 (accept_3_3 5 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 124 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 145 (accept_3_3 2 124 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 145 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 124 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 145)))))))))))))))))))))) (allB_succ' 23 123 145
  (Eq.refl Bool.true) (allA_succ_of_accept 22 123 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 123 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 123 145 (accept_3_3 20 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 123 145 (Polychromatic418967fa.accept_17_2_4_9_1_2791 19 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 123 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 145 (accept_3_3 17 123 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 123 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 145
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 123 145 (accept_3_3 14 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 123 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 123 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 123 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 145 (accept_3_3 11 123 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 123 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 145
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 123 145 (accept_3_3 8 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  123 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 123 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 145 (accept_3_3 5 123 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 123 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 123 145 (accept_3_3 2 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  123 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 123 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 123 145))))))))))))))))))))))) (allB_succ' 24 122 145 (Eq.refl Bool.true) (allA_of_3_1 24 122
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 121 145 (Eq.refl Bool.true) (allA_succ_of_accept 24 121
  145 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 121 145 (accept_3_3 23 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 121 145 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 121 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 121 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 145 (accept_3_3 20 121 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 145 (Polychromatic418967fa.accept_10_9_1_5_1_594
  19 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 145 (accept_3_3 17 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 121 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 145 (accept_3_3 14 121 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 121 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 145 (accept_3_3 11 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 121 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 145 (accept_3_3 8 121 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 121 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 145 (accept_3_3 5 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 121 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 121 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 145 (accept_3_3 2 121 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 145 (Polychromatic418967fa.accept_19_1_7_12_1_3443 1 121 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 145))))))))))))))))))))))))) (allB_succ' 26 120 145
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 120 145 5 5 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 120 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 120 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 120 145 (accept_3_3 23 120 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 120 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 120 145
  (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 145 5 4 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 145 (Polychromatic418967fa.accept_22_19_10_13_1_7775 19 120 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 120 145 (Polychromatic418967fa.accept_7_4_1_5_1_540
  18 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 120 145 (accept_3_3 17
  120 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 145
  (Polychromatic418967fa.accept_9_7_3_1_1_386 16 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 120 145 5 3 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 120 145 (accept_3_3 14 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 120 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 120 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 120 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 120 145 (accept_3_3 11 120 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 145 5 2 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 120 145 (Polychromatic418967fa.accept_13_9_3_2_1_399 9
  120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 120 145 (accept_3_3 8 120
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 145
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 120 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 120 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 120 145 5 1 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 120 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 120 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 120 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 120 145 (accept_3_3 2 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  120 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 120 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 120 145)))))))))))))))))))))))))) (allB_succ' 27 119 145 (Eq.refl Bool.true) (allA_of_3_1 27 119
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 118 145 (Eq.refl Bool.true) (allA_succ_of_accept 27 118
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 118 145 (accept_3_3 26 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 118 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 118 145 (Polychromatic418967fa.accept_19_5_4_12_1_7773 24 118 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 118 145 (accept_3_3 23 118 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 118 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 118 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 118 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 118 145 (accept_3_3 20 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 118 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 118 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 118 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 118 145 (accept_3_3 17 118 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 118 145 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 118 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 118 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 118 145 (accept_3_3 14 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 118 145 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 118 145 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 118 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 118 145 (accept_3_3 11 118 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 118 145 (Polychromatic418967fa.accept_17_10_16_9_1_5127 10 118
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 118 145 (accept_3_3 8 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  118 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 118 145 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 118 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 118 145 (accept_3_3 5 118 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 118 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 118 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 118 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 118 145 (accept_3_3 2 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  118 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 118 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 118 145)))))))))))))))))))))))))))) (allB_succ' 29 117 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 117 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 117 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 117 145 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 117
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 145 (accept_3_3 26 117
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 145
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 25 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 117 145 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 117 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 145 (accept_3_3 23 117 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 117 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 117 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 117 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 145 (accept_3_3 20 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 145 (Polychromatic418967fa.accept_22_19_7_13_1_6004 19 117 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 145 (Polychromatic418967fa.accept_10_8_7_5_1_602
  18 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 145 (accept_3_3 17
  117 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 145
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 117 145 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 117 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 145 (accept_3_3 14 117 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 145 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 117 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 117 145 (accept_3_3 11 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 117 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 117 145 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 117 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 117 145 (accept_3_3 8 117 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 145 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 117 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 117 145 (accept_3_3 5 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  117 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 117 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 117 145 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 117 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 145 (accept_3_3 2 117 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 145 (Polychromatic418967fa.accept_17_1_15_9_1_1743 1 117 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117 145))))))))))))))))))))))))))))) (allB_succ' 30 116
  145 (Eq.refl Bool.true) (allA_of_3_1 30 116 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 115 145
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 115 145 5 6 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 115 145 (accept_3_3 29 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 145 (Polychromatic418967fa.accept_19_9_1_12_1_6234 28 115 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 145 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 115
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 145 (accept_3_3 26 115
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 115 145 5 5 23 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 115 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 145 (accept_3_3 23 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 115 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 145 5 4 23 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 145
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 115 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 145 (accept_3_3 17 115 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 115 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 145 5 3 23 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 145 (accept_3_3 14 115 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 115 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 145 (accept_3_3 11 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 145 5 2 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 145 (accept_3_3 8 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 145 (Polychromatic418967fa.accept_19_7_1_12_1_6134 7 115 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 115 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 145 5 1 23 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 145
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 115 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 115 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 145 (accept_3_3 2 115 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 115 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115 145))))))))))))))))))))))))))))))) (allB_succ' 32 114 145
  (Eq.refl Bool.true) (allA_succ_of_accept 31 114 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 114 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 114 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 114 145 (accept_3_3 29 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 114 145 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 114 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 114 145 (accept_3_3 26 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 114 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 114 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 114 145 (accept_3_3 23 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 114 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 114 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 114 145 (accept_3_3 20 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 114 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 114 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 114 145 (accept_3_3 17 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 114 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 114 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 114 145 (accept_3_3 14 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 114 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 114 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 114 145 (accept_3_3 11 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 114 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 114 145 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 114 145 (accept_3_3 8 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 114 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 114 145
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 114 145 (accept_3_3 5 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  114 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 114 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 114 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 114 145 (accept_3_3 2 114 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 145 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 114 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 145)))))))))))))))))))))))))))))))) (allB_succ' 33
  113 145 (Eq.refl Bool.true) (allA_of_3_1 33 113 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 112 145
  (Eq.refl Bool.true) (allA_succ_of_accept 33 112 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 145 (accept_3_3 32 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 112 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 112
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 112 145 (accept_3_3 29 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 112 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 112 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 145 (accept_3_3 26 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 112 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 112 145 (accept_3_3 23 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 112 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 112 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 145 (accept_3_3 20 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 112 145 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 112 145 (accept_3_3 17 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 112 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 112 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 145 (accept_3_3 14 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 112 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 145 (accept_3_3 11 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 145 (accept_3_3 8 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 145 (accept_3_3 5 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 112 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 145 (accept_3_3 2 112 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 112 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112 145)))))))))))))))))))))))))))))))))) (allB_succ' 35
  111 145 (Eq.refl Bool.true) (allA_succ_of_accept 34 111 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 111 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 111 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 111 145 (accept_3_3 32 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 111 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 111 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 111 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 145 (accept_3_3 29 111 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 111 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 111 145
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 145 (accept_3_3 26 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 111 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 111 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 145 (accept_3_3 23 111 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 111 145
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 111 145 (accept_3_3 20 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 111 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 111 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 111 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 145 (accept_3_3 17 111 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 111 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 111 145
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 111 145 (accept_3_3 14 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 111 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 111 145 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 111 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 145 (accept_3_3 11 111 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 111 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 111 145
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 111 145 (accept_3_3 8 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  111 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 111 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 111 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 145 (accept_3_3 5 111 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 111 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 111 145
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 111 145 (accept_3_3 2 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  111 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 111 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 111 145))))))))))))))))))))))))))))))))))) (allB_succ' 36 110 145 (Eq.refl Bool.true)
  (allA_of_3_1 36 110 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 109 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 109 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 109 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 145 (accept_3_3 35 109 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 109 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 145 (Polychromatic418967fa.accept_13_7_5_2_1_401
  33 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 145 (accept_3_3 32
  109 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 145
  (Polychromatic418967fa.accept_10_1_9_5_1_83 31 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 109 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 109 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 145 (accept_3_3 29 109 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 109 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 145 (Polychromatic418967fa.accept_7_6_4_5_1_314
  27 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 145 (accept_3_3 26
  109 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 145
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 109 145 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 109 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 145 (accept_3_3 23 109 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 109 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 145 (Polychromatic418967fa.accept_10_1_9_5_1_83
  21 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 145 (accept_3_3 20
  109 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 145
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 109 145 (Polychromatic418967fa.accept_21_18_4_19_1_1838 18 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 145 (accept_3_3 17 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 109 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 145
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 145 (accept_3_3 14 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 145 (accept_3_3 11 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 145 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 109 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 145
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 145 (accept_3_3 8 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 145 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 145 (accept_3_3 5 109 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 109 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 145
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 145 (accept_3_3 2 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 109 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 145))))))))))))))))))))))))))))))))))))) (allB_succ' 38 108 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 108 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 108 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 108 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 108 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 108 145 (accept_3_3 35 108 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 145
  (Polychromatic418967fa.accept_16_2_12_1_1_3086 34 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 108 145 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 108 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 108 145 (accept_3_3 32 108 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 108 145 (Polychromatic418967fa.accept_13_5_4_2_1_846 31 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 108 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 108 145 (accept_3_3 29 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 108 145 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 108 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 108 145 (accept_3_3 26 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 145 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 108
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 108 145
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 108 145 (accept_3_3 23 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 108 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 108 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 108 145 (accept_3_3 20 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 145 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 108 145
  (Polychromatic418967fa.accept_11_7_9_2_1_260 18 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 108 145 (accept_3_3 17 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 108 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 108 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 108 145 (accept_3_3 14 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 108 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 108 145
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 108 145 (accept_3_3 11 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 108 145 (Polychromatic418967fa.accept_20_10_8_5_1_7735 10 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 108 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 108 145 (accept_3_3 8 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 108 145
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 108 145 (accept_3_3 5 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  108 145 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 108 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 108 145 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 108 145 (accept_3_3 2 108 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 108 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 108 145))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 107 145 (Eq.refl Bool.true) (allA_of_3_1 39 107 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 106 145 (Eq.refl Bool.true) (allA_succ_of_accept 39 106 145 (Polychromatic418967fa.accept_4_3_2_1_1_50
  39 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 145 (accept_3_3 38
  106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 145
  (Polychromatic418967fa.accept_15_7_1_10_1_305 37 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 106 145 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 106 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 106 145 (accept_3_3 35 106 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 106 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33
  106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 145 (accept_3_3 32
  106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 106 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 106 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 106 145 (accept_3_3 29 106 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 106 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 106 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 106 145 (accept_3_3 26 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 106 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 106 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 106 145 (accept_3_3 23 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 106 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 106 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 106 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 106 145 (accept_3_3 20 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 106 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 106 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 106 145 (accept_3_3 17 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 106 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 106 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 106 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 106 145 (accept_3_3 14 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 106 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 106 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 106 145 (accept_3_3 11 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 106 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 106 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 106 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 106 145 (accept_3_3 8 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  106 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 106 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 106 145 (accept_3_3 5 106 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 106 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 106 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 106 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 106 145 (accept_3_3 2 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  106 145 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 106 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 106 145)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 105 145 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 105 145 5 8 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 105 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 145 (accept_3_3 38 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 105 145 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 105 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 105 145
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 36 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 105 145 5 7 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 105 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 105 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 145
  (Polychromatic418967fa.accept_19_14_10_12_1_4809 33 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 105 145 (accept_3_3 32 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 145 5 6 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 145 (accept_3_3 29 105 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 105 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 145
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 105 145 (accept_3_3 26 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  105 145 5 5 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 105 145 (Polychromatic418967fa.accept_16_8_9_1_1_7753 24 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 145 (accept_3_3 23 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 105 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 105 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 105 145 5 4 21 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 145
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 105 145 (Polychromatic418967fa.accept_16_2_9_1_1_6404 18 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 105 145 (accept_3_3 17 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 105 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 105 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 145 5 3 21 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 145 (accept_3_3 14 105 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 105 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 105 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 105 145 (accept_3_3 11 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  105 145 5 2 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 105 145 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 105 145 (accept_3_3 8 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 105 145 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 105 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 105 145 5 1 21 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 145
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 105 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 105 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 145 (accept_3_3 2 105 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 105 145 (Polychromatic418967fa.accept_17_1_3_9_1_958 1 105 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105 145))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 104
  145 (Eq.refl Bool.true) (allA_of_3_1 42 104 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 103 145
  (Eq.refl Bool.true) (allA_succ_of_accept 42 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 145 (accept_3_3 41 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 145 (Polychromatic418967fa.accept_13_1_12_2_1_384 40 103
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 145 (accept_3_3 38 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 145 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 145 (accept_3_3 35 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 103 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 145 (accept_3_3 32 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 145 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 145 (accept_3_3 29 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 145 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 145
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 145 (accept_3_3 26 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 145 (accept_3_3 23 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 145 (accept_3_3 20 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 145 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 145 (accept_3_3 17 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 145 (accept_3_3 14 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 145 (Polychromatic418967fa.accept_24_13_7_1_1_7774 13 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 145 (accept_3_3 11 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 145
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 145 (accept_3_3 8 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 145 (accept_3_3 5 103 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 145 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 103 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 145 (accept_3_3 2 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 145 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 103 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 145))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 102 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 102 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 102 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 102 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 102 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 102 145 (accept_3_3 41 102 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 145 (Polychromatic418967fa.accept_9_4_3_1_1_154
  40 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 102 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 102 145 (accept_3_3 38 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 102 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 102 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 102 145 (accept_3_3 35 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 102 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 102 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 102 145 (accept_3_3 32 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 102 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 102 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 102 145 (accept_3_3 29 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 102 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 102 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 102 145 (accept_3_3 26 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 102 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 102 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 102 145 (accept_3_3 23 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 102 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 102 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 102 145 (accept_3_3 20 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 102 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 102 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 102
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 102 145 (accept_3_3 17 102
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 145
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 102 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 102 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 102 145 (accept_3_3 14 102 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 102 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 102 145 (Polychromatic418967fa.accept_11_1_3_2_1_1090
  12 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 102 145 (accept_3_3 11
  102 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 145
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 102 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 102 145 (accept_3_3 8 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 102 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 102 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 102 145 (accept_3_3 5 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  102 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 102 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 102 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 102 145 (accept_3_3 2 102 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 102 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 145))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 101 145 (Eq.refl Bool.true) (allA_of_3_1 45 101 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 100 145 (Eq.refl Bool.true) (allA_succ_of_gcd 45 100 145 5 9 20 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 100 145 (accept_3_3 44 100 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 145 (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 100
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 145
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 145 (accept_3_3 41 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  100 145 5 8 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 100 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 100 145 (accept_3_3 38 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 100 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 145 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 100
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 100 145 5 7 20 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 100 145
  (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 100 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 145 (accept_3_3 32 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 100 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 100 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 145 5 6 20 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 145 (accept_3_3 29 100 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 145 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 100
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 100 145 (accept_3_3 26 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  100 145 5 5 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 100 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 100 145 (accept_3_3 23 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 100 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 100 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 145 5 4 20 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 145
  (Polychromatic418967fa.accept_13_6_9_2_1_838 19 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 100 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 145 (accept_3_3 17 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 100 145 (Polychromatic418967fa.accept_13_3_9_2_1_1486 16 100 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 100 145 5 3 20 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 100 145 (accept_3_3 14 100 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 145 (Polychromatic418967fa.accept_8_5_4_1_1_111
  13 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 145
  (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 145 (accept_3_3 11 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 145 5 2 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 100 145 (accept_3_3 8 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 100 145 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 145 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 100 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 100 145 5 1 20 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 100 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 145 (accept_3_3 2 100 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 145 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 100 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 145)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  47 99 145 (Eq.refl Bool.true) (allA_succ_of_accept 46 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 99 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 99 145 (accept_3_3 44 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  99 145 (Polychromatic418967fa.accept_19_5_4_12_1_7773 43 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 145 (accept_3_3 41 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 145
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 99 145 (accept_3_3 38 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  99 145 (Polychromatic418967fa.accept_25_12_24_20_1_7772 37 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 99 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 145 (accept_3_3 35 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 99 145 (accept_3_3 32 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  99 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 145 (accept_3_3 29 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 145
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 99 145 (accept_3_3 26 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  99 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 99 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 145 (accept_3_3 23 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 145
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 99 145 (accept_3_3 20 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  99 145 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 145 (accept_3_3 17 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 145
  (Polychromatic418967fa.accept_20_15_19_5_1_7718 15 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 99 145 (accept_3_3 14 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  99 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 99 145 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 145 (accept_3_3 11 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 99 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 145 (accept_3_3 8 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99
  145 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 145 (accept_3_3 5 99 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 99 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 99 145 (accept_3_3 2 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99
  145 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 99 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 99 145))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 98 145 (Eq.refl Bool.true) (allA_of_3_1
  48 98 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 97 145 (Eq.refl Bool.true) (allA_succ_of_accept 48
  97 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 97 145 (accept_3_3 47 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 97 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 97 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 97 145 (Polychromatic418967fa.accept_22_1_9_13_1_2894 45 97
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 145 (accept_3_3 44 97 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 97 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 43
  97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 97 145 (accept_3_3 41 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  97 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 97 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 145 (accept_3_3 38 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 97 145 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 97 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 145
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 97 145 (accept_3_3 35 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  97 145 (Polychromatic418967fa.accept_13_8_6_2_1_865 34 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 97 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 145 (accept_3_3 32 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 97 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 145 (accept_3_3 29 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 145 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 145 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 145 (accept_3_3 26 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 97 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 145 (accept_3_3 23 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 145 (accept_3_3 20 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 97 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 145
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 145 (accept_3_3 17 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 145 (accept_3_3 14 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 97 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 145 (accept_3_3 11 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 145 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 145 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 145 (accept_3_3 8 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 145 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 97 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 145 (accept_3_3 5 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 97 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 97 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 97 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 145 (accept_3_3 2 97 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 97 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 97 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 145))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  50 96 145 (Eq.refl Bool.true) (allA_succ_of_accept 49 96 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 96 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 96 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 96 145 (accept_3_3 47 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  96 145 (Polychromatic418967fa.accept_13_7_5_2_1_401 46 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 96 145 (Polychromatic418967fa.accept_14_3_12_5_1_153 45 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 96 145 (accept_3_3 44 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 96 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 96 145
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 42 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 96 145 (accept_3_3 41 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  96 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 96 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 96 145 (accept_3_3 38 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 96 145 (Polychromatic418967fa.accept_17_3_11_9_1_5100 37 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 96 145
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 96 145 (accept_3_3 35 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  96 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 96 145 (Polychromatic418967fa.accept_13_7_5_2_1_401 33 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 96 145 (accept_3_3 32 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 96 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 96 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 96 145 (accept_3_3 29 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  96 145 (Polychromatic418967fa.accept_19_9_1_12_1_6234 28 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 96 145 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 96 145 (accept_3_3 26 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 96 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 96 145
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 96 145 (accept_3_3 23 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  96 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 96 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 96 145 (accept_3_3 20 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 96 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 96 145
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 96 145 (accept_3_3 17 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  96 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 96 145 (Polychromatic418967fa.accept_20_15_16_5_1_7771 15 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 96 145 (accept_3_3 14 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 96 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 96 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 96 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 96 145 (accept_3_3 11 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  96 145 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 96 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 96 145 (accept_3_3 8 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 96 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 96 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 96 145
  (Polychromatic418967fa.accept_21_6_12_19_1_6032 6 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 96 145 (accept_3_3 5 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 96
  145 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 96 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 96 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 96 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 96 145 (accept_3_3 2 96 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 96 145 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 96 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96 145))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 95 145 (Eq.refl Bool.true) (allA_of_3_1 51 95 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  52 94 145 (Eq.refl Bool.true) (allA_succ_of_accept 51 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 94 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 94 145 (accept_3_3 50 94 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 94 145 (Polychromatic418967fa.accept_10_9_4_5_1_616
  49 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 94 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 94 145 (accept_3_3 47 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  94 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 94 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 94 145 (accept_3_3 44 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 94 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 94 145 (accept_3_3 41 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  94 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 94 145 (accept_3_3 38 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 94 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 94 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 94 145 (accept_3_3 35 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  94 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 94 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 94 145 (accept_3_3 32 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 94 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 94 145 (accept_3_3 29 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  94 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 94 145 (accept_3_3 26 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 94 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 94 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 94 145 (accept_3_3 23 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  94 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 94 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 94 145 (accept_3_3 20 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 94 145
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 94 145 (accept_3_3 17 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  94 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 94 145 (accept_3_3 14 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 94 145 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 94 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 94 145 (accept_3_3 11 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  94 145 (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 94 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 94 145 (accept_3_3 8 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 94 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 94 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 94 145 (accept_3_3 5 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 94
  145 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 94 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 94 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 94 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 94 145 (accept_3_3 2 94 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 94 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 94 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94 145))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 93 145 (Eq.refl Bool.true) (allA_succ_of_accept 52 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 93 145 (accept_3_3 50 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  93 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 93 145 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 93 145 (accept_3_3 47 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 93 145 (accept_3_3 44 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  93 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 93 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 93 145 (accept_3_3 41 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 93 145 (accept_3_3 38 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  93 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 93 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 93 145 (accept_3_3 35 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 93 145 (accept_3_3 32 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  93 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 93 145 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 93 145 (accept_3_3 29 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 145
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 93 145 (accept_3_3 26 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  93 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 93 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 93 145 (accept_3_3 23 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 145
  (Polychromatic418967fa.accept_14_7_9_5_1_529 21 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 93 145 (accept_3_3 20 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  93 145 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 93 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 145 (accept_3_3 17 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 93 145 (accept_3_3 14 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  93 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 93 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 93 145 (accept_3_3 11 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 93 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 145
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 93 145 (accept_3_3 8 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93
  145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 93 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 93 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 93 145 (accept_3_3 5 93 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 93 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 93 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 93 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 145 (accept_3_3 2 93 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 145 (Polychromatic418967fa.accept_17_1_8_9_1_1810 1
  93 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  145))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 92 145 (Eq.refl Bool.true) (allA_of_3_1 54 92
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 91 145 (Eq.refl Bool.true) (allA_succ_of_accept 54 91 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 91 145 (accept_3_3 53 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 145 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 145 (Polychromatic418967fa.accept_14_9_7_5_1_1105 51 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 145 (accept_3_3 50 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 145
  (Polychromatic418967fa.accept_22_4_3_13_1_7770 48 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 145 (accept_3_3 47 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 145 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 145 (accept_3_3 44 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 145 (accept_3_3 41 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 145 (Polychromatic418967fa.accept_14_12_7_5_1_1107 40 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 145 (accept_3_3 38 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 145 (Polychromatic418967fa.accept_14_9_7_5_1_1105 37 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 145
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 145 (accept_3_3 35 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 145 (Polychromatic418967fa.accept_17_16_6_9_1_7769 33 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 145 (accept_3_3 32 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 145 (Polychromatic418967fa.accept_16_15_11_1_1_7767 31 91
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 145 (accept_3_3 29 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 145 (Polychromatic418967fa.accept_19_8_15_12_1_2240 27 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 145 (accept_3_3 26 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 145 (Polychromatic418967fa.accept_17_8_6_9_1_7768 25 91 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 145
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 145 (accept_3_3 23 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 145 (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 145 (accept_3_3 20 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 91 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 91 145 (accept_3_3 17 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  91 145 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 91 145 (Polychromatic418967fa.accept_16_15_11_1_1_7767 15 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 145 (accept_3_3 14 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 91
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 145
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 145 (accept_3_3 11 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 145 (accept_3_3 8 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 145 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 145 (accept_3_3 5 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  145 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 91 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 145 (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 145 (accept_3_3 2 91 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 145 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 91 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 90 145 (Eq.refl Bool.true) (allA_succ_of_gcd
  55 90 145 5 11 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 90 145 (Polychromatic418967fa.accept_19_16_14_12_1_6261 54 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 90 145 (accept_3_3 53 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 90 145 (Polychromatic418967fa.accept_20_12_10_5_1_4661 52 90 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 90 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 90 145 5 10 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 90 145 (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 90 145 (Polychromatic418967fa.accept_17_14_5_9_1_7766 48 90
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 90 145 (accept_3_3 47 90 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 90 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 46
  90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 90 145 5 9 18 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 90 145 (accept_3_3 44
  90 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 90 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 90 145 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 90 145 (accept_3_3 41 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 90 145 5 8 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 90 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 90 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 90 145 (accept_3_3 38 90 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 90 145 (Polychromatic418967fa.accept_20_17_10_5_1_7765 37 90 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 90 145
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 90 145 5 7 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 90 145 (Polychromatic418967fa.accept_20_14_10_5_1_2117 34 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 90 145 (Polychromatic418967fa.accept_20_13_10_5_1_3338 33 90
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 90 145 (accept_3_3 32 90 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 90 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 145 5 6 18 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 145 (accept_3_3 29
  90 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 90 145
  (Polychromatic418967fa.accept_19_9_14_12_1_7764 28 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 90 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 90 145 (accept_3_3 26 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 90 145 5 5 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 90 145 (Polychromatic418967fa.accept_17_7_5_9_1_7763 24 90 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 90 145 (accept_3_3 23 90 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 90 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 90 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 90 145
  (Polychromatic418967fa.accept_19_2_14_12_1_7762 21 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 145 5 4 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 90 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 90 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 90 145 (accept_3_3 17 90 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 90 145 (Polychromatic418967fa.accept_13_3_12_2_1_385
  16 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 90 145 5 3 18 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 90 145 (accept_3_3 14
  90 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 90 145
  (Polychromatic418967fa.accept_14_13_6_5_1_1853 13 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 90 145 (Polychromatic418967fa.accept_17_12_5_9_1_6372 12 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 90 145 (accept_3_3 11 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 145 5 2 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 145 (Polychromatic418967fa.accept_16_9_10_1_1_2998 9 90 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 90 145 (accept_3_3 8 90 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 90 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 90 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 90 145
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 90 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 90 145 5 1 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 90 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 90 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 90 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 90 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 90 145 (accept_3_3 2 90 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 90 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 90
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 89 145 (Eq.refl Bool.true) (allA_of_3_1 57
  89 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 88 145 (Eq.refl Bool.true) (allA_succ_of_accept 57 88
  145 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 88 145 (accept_3_3 56 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  88 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 88 145 (Polychromatic418967fa.accept_20_14_8_5_1_6090 54 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 88 145 (accept_3_3 53 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 88 145 (Polychromatic418967fa.accept_10_2_8_5_1_587 52 88 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 88 145 (accept_3_3 50 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  88 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 88 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 88 145 (accept_3_3 47 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 88 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 88 145 (accept_3_3 44 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  88 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 88 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 88 145 (accept_3_3 41 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 88 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 88 145 (accept_3_3 38 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  88 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 88 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 88 145 (accept_3_3 35 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 88 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 88 145 (accept_3_3 32 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  88 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 88 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 88 145 (accept_3_3 29 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 88 145 (Polychromatic418967fa.accept_16_12_8_1_1_5270 28 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 88 145 (accept_3_3 26 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  88 145 (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 88 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 88 145 (accept_3_3 23 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 88 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 88 145 (accept_3_3 20 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  88 145 (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 88 145 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 88 145 (accept_3_3 17 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 88 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 88 145 (accept_3_3 14 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  88 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 88 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 88 145 (accept_3_3 11 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 88 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 88 145 (accept_3_3 8 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 88
  145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 88 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 88 145 (accept_3_3 5 88 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 88 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 88 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 88 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 88 145 (accept_3_3 2 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 88
  145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 88 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 87 145 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 87 145 29 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 87 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 87 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 145 (accept_3_3 56 87 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 87 145 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 87 145 (accept_3_3 53 87
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 145 (Polychromatic418967fa.accept_6_4_3_1_1_57
  52 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 87 145 (accept_3_3 50 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  87 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 87 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 87 145 (accept_3_3 47 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 145
  (Polychromatic418967fa.accept_11_1_10_2_1_58 45 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 87 145 (accept_3_3 44 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  87 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 87 145 (accept_3_3 41 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 87 145 (accept_3_3 38 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  87 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 87 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 87 145 (accept_3_3 35 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 145
  (Polychromatic418967fa.accept_10_3_7_5_1_288 33 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 87 145 (accept_3_3 32 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  87 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 29 87 145 29 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 28 87 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 145
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 87 145 (accept_3_3 26 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  87 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 87 145 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 87 145 (accept_3_3 23 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 87 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 87 145 (accept_3_3 20 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  87 145 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 87 145 (accept_3_3 17 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 87 145 (accept_3_3 14 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  87 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 87 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 87 145 (accept_3_3 11 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 87 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 87 145 (accept_3_3 8 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 87
  145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 87 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 87 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 87 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 87 145 (accept_3_3 5 87 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 87 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 87 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 87 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 87
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 145 (accept_3_3 2 87 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 87
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 86 145 (Eq.refl Bool.true) (allA_of_3_1
  60 86 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 85 145 (Eq.refl Bool.true) (allA_succ_of_gcd 60 85
  145 5 12 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  85 145 (accept_3_3 59 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 85 145
  (Polychromatic418967fa.accept_19_1_9_12_1_6207 58 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 85 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 145 (accept_3_3 56 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 85 145 5 11 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 85 145 (Polychromatic418967fa.accept_16_6_5_1_1_7761 54 85 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 85 145 (accept_3_3 53 85 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 85 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 85 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 85 145 5 10 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 85 145 (Polychromatic418967fa.accept_11_5_8_2_1_588 49 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 85 145 (accept_3_3 47 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 85 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 46
  85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 85 145 5 9 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 85 145 (accept_3_3 44
  85 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 145
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 85 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 85 145 (accept_3_3 41 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 85 145 5 8 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 85 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 85 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 145 (accept_3_3 38 85 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 145 (Polychromatic418967fa.accept_19_18_9_12_1_6153 37 85 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 85 145 5 7 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 85 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 85 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 145 (accept_3_3 32 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 31
  85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 85 145 5 6 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 85 145 (accept_3_3 29
  85 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 85 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 28 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 85 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 145 (accept_3_3 26 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 85 145 5 5 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 85 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 85 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 85 145 (accept_3_3 23 85 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 85 145 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 85 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 85 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 85 145 5 4 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 85 145 (Polychromatic418967fa.accept_23_19_16_7_1_7760 19 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 85 145 (accept_3_3 17 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 85 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16
  85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 85 145 5 3 17 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 85 145 (accept_3_3 14
  85 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 145
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 85 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 85 145 (accept_3_3 11 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 85 145 5 2 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 85 145 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 85 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 145 (accept_3_3 8 85 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 85 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 145
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 85 145 5 1 17 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 85 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 85 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 85 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 145 (accept_3_3 2 85 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 145 (Polychromatic418967fa.accept_19_1_9_12_1_6207
  1 85 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 84 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 84 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 84 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 84 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 84 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 84 145 (accept_3_3 59 84 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 84 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 58
  84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 84 145
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 84 145 (accept_3_3 56 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  84 145 (Polychromatic418967fa.accept_20_15_4_5_1_7759 55 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 84 145 (Polychromatic418967fa.accept_23_8_15_7_1_7758 54 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 84 145 (accept_3_3 53 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 84 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 84 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 84 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 84 145 (accept_3_3 50 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  84 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 84 145 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 84 145 (accept_3_3 47 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 84 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 84 145
  (Polychromatic418967fa.accept_8_5_4_1_1_111 45 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 84 145 (accept_3_3 44 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  84 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 84 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 84 145 (accept_3_3 41 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 84 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 84 145
  (Polychromatic418967fa.accept_10_9_4_5_1_616 39 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 84 145 (accept_3_3 38 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  84 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 84 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 84 145 (accept_3_3 35 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 84 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 84 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 84 145 (accept_3_3 32 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  84 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 84 145 (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 84 145 (accept_3_3 29 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 84 145 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 84 145
  (Polychromatic418967fa.accept_13_1_6_2_1_377 27 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 84 145 (accept_3_3 26 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  84 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 84 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 84 145 (accept_3_3 23 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 84 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 84 145
  (Polychromatic418967fa.accept_8_5_4_1_1_111 21 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 84 145 (accept_3_3 20 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  84 145 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 84 145 (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 84 145 (accept_3_3 17 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 84 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 84 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 84 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 84 145 (accept_3_3 14 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  84 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 84 145 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 84 145 (accept_3_3 11 84 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 84 145 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 84
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 84 145
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 84 145 (accept_3_3 8 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 84
  145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 84 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 84 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 84 145 (accept_3_3 5 84 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 84 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 84 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 84 145 (Polychromatic418967fa.accept_15_3_9_10_1_2325
  3 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 84 145 (accept_3_3 2 84
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 84 145
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 84 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 84 145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 83 145 (Eq.refl
  Bool.true) (allA_of_3_1 63 83 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 82 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 82 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 82 145 (accept_3_3 62 82 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 82 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 82 145 (Polychromatic418967fa.accept_16_12_2_1_1_1215
  60 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 82 145 (accept_3_3 59
  82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 82 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 58 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 82 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 82 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 82 145 (accept_3_3 56 82 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 82 145 (Polychromatic418967fa.accept_16_6_2_1_1_4081
  54 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 82 145 (accept_3_3 53
  82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 82 145
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 52 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 82 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 82 145 (accept_3_3 50 82 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 82 145 (Polychromatic418967fa.accept_14_7_12_5_1_1861 49 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 82 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 82 145 (accept_3_3 47 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  82 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 46 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 82 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 82 145 (accept_3_3 44 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 82 145
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 82 145 (accept_3_3 41 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  82 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 82 145 (accept_3_3 38 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 82 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 82 145
  (Polychromatic418967fa.accept_19_17_6_12_1_7757 36 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 82 145 (accept_3_3 35 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  82 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 34 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 82 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 82 145 (accept_3_3 32 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 82 145
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 82 145 (accept_3_3 29 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  82 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 82 145 (accept_3_3 26 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 82 145 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 82 145
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 82 145 (accept_3_3 23 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  82 145 (Polychromatic418967fa.accept_16_6_2_1_1_4081 22 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 82 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 82 145 (accept_3_3 20 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 82 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 82 145 (accept_3_3 17 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  82 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 82 145 (accept_3_3 14 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 82 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 82 145
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 82 145 (accept_3_3 11 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  82 145 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 82 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 82 145 (accept_3_3 8 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 82 145
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 82 145 (accept_3_3 5 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 82
  145 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 82 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 82 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 82 145 (accept_3_3 2 82 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 82 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 82 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 81 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 81 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 145 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 81 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 145 (accept_3_3 62 81 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 145 (Polychromatic418967fa.accept_11_6_4_2_1_599
  61 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 145
  (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 81 145 (accept_3_3 59 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 145 (accept_3_3 56 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 81 145
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 81 145 (accept_3_3 53 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 81 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 145 (accept_3_3 50 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 81 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 81 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 81 145 (accept_3_3 47 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 81 145 (Polychromatic418967fa.accept_19_7_5_12_1_7756 45 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 145 (accept_3_3 44 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 81 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 81 145
  (Polychromatic418967fa.accept_11_9_4_2_1_600 42 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 81 145 (accept_3_3 41 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 81 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 145 (accept_3_3 38 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 81 145
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 81 145 (accept_3_3 35 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 81 145 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 145 (accept_3_3 32 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 81 145 (Polychromatic418967fa.accept_11_9_4_2_1_600 31 81 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 81 145
  (Polychromatic418967fa.accept_7_2_4_5_1_313 30 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 81 145 (accept_3_3 29 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 81 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 145 (accept_3_3 26 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 145 (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 81 145
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 81 145 (accept_3_3 23 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 81 145 (Polychromatic418967fa.accept_17_4_13_9_1_921 21 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 145 (accept_3_3 20 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 81 145
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 81 145 (accept_3_3 17 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 81 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 145 (accept_3_3 14 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 81 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 81 145
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 81 145 (accept_3_3 11 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  81 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 81 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 145 (accept_3_3 8 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 145 (Polychromatic418967fa.accept_19_7_5_12_1_7756 7 81 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 145 (accept_3_3 5 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81
  145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 81 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 81 145 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 81 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 145 (accept_3_3 2 81 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 81 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 81 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 80 145 (Eq.refl Bool.true)
  (allA_of_3_1 66 80 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 79 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 79 145 (accept_3_3 65 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 145 (Polychromatic418967fa.accept_10_4_9_5_1_84 64 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 145 (Polychromatic418967fa.accept_14_7_9_5_1_529
  63 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 79 145 (accept_3_3 62
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 79 145
  (Polychromatic418967fa.accept_10_1_9_5_1_83 61 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 79 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 145 (accept_3_3 59 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 57
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 79 145 (accept_3_3 56 79
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 79 145
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 145 (accept_3_3 53 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 79 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 52 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 51
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 79 145 (accept_3_3 50 79
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 79 145
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 79 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 145 (accept_3_3 47 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 45
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 79 145 (accept_3_3 44 79
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 79 145
  (Polychromatic418967fa.accept_15_13_4_10_1_821 43 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 145 (accept_3_3 41 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 79 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 39
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 79 145 (accept_3_3 38 79
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 79 145
  (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 79 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 145 (accept_3_3 35 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 33
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 79 145 (accept_3_3 32 79
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 79 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 31 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 145 (accept_3_3 29 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 79 145 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 79 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 145
  (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 145 (accept_3_3 26 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 145 (accept_3_3 23 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 79 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 145 (accept_3_3 20 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 145 (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 145 (accept_3_3 17 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 79 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 145 (accept_3_3 14 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 145 (accept_3_3 11 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 79 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 145
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 145 (accept_3_3 8 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  145 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 79 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 145 (accept_3_3 5 79 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 79 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 79 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 79 145 (accept_3_3 2 79 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79 145 (Polychromatic418967fa.accept_10_1_9_5_1_83 1
  79 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 79
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 78 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 78 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 78 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 78 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 78 145 (accept_3_3 65 78 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 78 145 (Polychromatic418967fa.accept_17_13_10_9_1_946
  64 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 78 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 63 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 78 145 (accept_3_3 62 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  78 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 78 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 78 145 (accept_3_3 59 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 78 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 78 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 78 145 (accept_3_3 56 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  78 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 78 145 (Polychromatic418967fa.accept_11_10_1_2_1_1624 54 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 78 145 (accept_3_3 53 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 78 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 78 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 78 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 78 145 (accept_3_3 50 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  78 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 78 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 78 145 (accept_3_3 47 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 78 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 78 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 78 145 (accept_3_3 44 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  78 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 78 145 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 78 145 (accept_3_3 41 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 78 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 78 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 78 145 (accept_3_3 38 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  78 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 78 145 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 78 145 (accept_3_3 35 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 78 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 78 145
  (Polychromatic418967fa.accept_10_3_8_5_1_606 33 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 78 145 (accept_3_3 32 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  78 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 78 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 78 145 (accept_3_3 29 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 78 145 (Polychromatic418967fa.accept_15_13_3_10_1_2296 28 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 78 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 78 145 (accept_3_3 26 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  78 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 78 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 78 145 (accept_3_3 23 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 78 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 78 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 78 145 (accept_3_3 20 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  78 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 78 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 78 145 (accept_3_3 17 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 78 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 78 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 78 145 (accept_3_3 14 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  78 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 78 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 78 145 (accept_3_3 11 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 78 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 78 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 78 145
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 78 145 (accept_3_3 8 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 78
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 78 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 78 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 78 145 (accept_3_3 5 78 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 78 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 78 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 78 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 78
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 78 145 (accept_3_3 2 78 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 78 145 (Polychromatic418967fa.accept_17_1_10_9_1_3884
  1 78 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 77 145 (Eq.refl Bool.true)
  (allA_of_3_1 69 77 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 76 145 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 76 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 76 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 76 145 (accept_3_3 68 76 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 76 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 76 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 66
  76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 76 145 (accept_3_3 65 76
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 76 145 (Polychromatic418967fa.accept_7_1_6_5_1_39
  64 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 76 145 (accept_3_3 62 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  76 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 76 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 76 145 (accept_3_3 59 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 76 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 76 145 (accept_3_3 56 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  76 145 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 76 145 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 76 145 (accept_3_3 53 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 76 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 76 145 (accept_3_3 50 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  76 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 49 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 76 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 76 145 (accept_3_3 47 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 76 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 46 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 76 145 (accept_3_3 44 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  76 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 76 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 76 145 (accept_3_3 41 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 76 145 (Polychromatic418967fa.accept_16_8_12_1_1_7720 40 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 76 145 (accept_3_3 38 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  76 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 76 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 76 145 (accept_3_3 35 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 76 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 76 145 (accept_3_3 32 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  76 145 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 76 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 76 145 (accept_3_3 29 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 76 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 76 145 (accept_3_3 26 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  76 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 76 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 76 145 (accept_3_3 23 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 76 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 76 145 (accept_3_3 20 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  76 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 76 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 76 145 (accept_3_3 17 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 76 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 76 145 (accept_3_3 14 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  76 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 76 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 76 145 (accept_3_3 11 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 76 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 76 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 76 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 76 145 (accept_3_3 8 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 76
  145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 76 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 76 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 76 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 76 145 (accept_3_3 5 76 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 76 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 76 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 76 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 76
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 76 145 (accept_3_3 2 76 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 76 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 76
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 76
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 75 145 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 75 145 5 14 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 75 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 145 (accept_3_3 68 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 75 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 75 145 5 13 15 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 75 145
  (Polychromatic418967fa.accept_6_4_3_1_1_57 64 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 75 145 (Polychromatic418967fa.accept_13_11_10_2_1_3840 63 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 145 (accept_3_3 62 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 75 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 145 5 12 15 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 145 (accept_3_3 59 75 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 75 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 75 145 (accept_3_3 56 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 75
  145 5 11 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 145 (accept_3_3 53 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 75 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 75 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 75 145 5 10 15 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 75 145
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 75 145 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 75 145 (accept_3_3 47 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 75 145 5 9 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 75 145 (accept_3_3 44 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 75 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 75 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 75 145 (accept_3_3 41 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 75
  145 5 8 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  75 145 (Polychromatic418967fa.accept_17_5_7_9_1_5122 39 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 75 145 (accept_3_3 38 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 145 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 75 145 (Polychromatic418967fa.accept_17_2_7_9_1_2796 36 75 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 75 145 5 7 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 75 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 75 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 145 (accept_3_3 32 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 75 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 145 5 6 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 145 (accept_3_3 29 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 75 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 145
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 27 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 75 145 (accept_3_3 26 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 75
  145 5 5 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  75 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 145 (accept_3_3 23 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 145 (Polychromatic418967fa.accept_12_9_3_1_1_303 21 75 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 75 145 5 4 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 75 145
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 75 145 (accept_3_3 17 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 75 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 145 5 3 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 145 (accept_3_3 14 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 75 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 75 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 75 145
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 75 145 (accept_3_3 11 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 75
  145 5 2 15 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  75 145 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 75 145 (accept_3_3 8 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 75 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 75 145 5 1 15 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 75 145
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 75 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 75 145 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 145 (accept_3_3 2 75 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 75 145 (Polychromatic418967fa.accept_19_1_18_12_1_7755 1 75 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 74 145 (Eq.refl Bool.true)
  (allA_of_3_1 72 74 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 73 145 (allA_succ_of_accept 72 73 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 72 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 73 145 (accept_3_3 71 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70
  73 145 (Polychromatic418967fa.accept_19_13_16_12_1_6096 70 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 73 145 (Polychromatic418967fa.accept_16_5_9_1_1_2070 69 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 73 145 (accept_3_3 68 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 73 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 73 145
  (Polychromatic418967fa.accept_16_2_9_1_1_6404 66 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 73 145 (accept_3_3 65 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  73 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 64 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 73 145 (Polychromatic418967fa.accept_15_3_13_10_1_2332 63 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 73 145 (accept_3_3 62 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 73 145 (Polychromatic418967fa.accept_15_1_13_10_1_1507 61 73
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 73 145
  (Polychromatic418967fa.accept_22_16_7_13_1_7754 60 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 73 145 (accept_3_3 59 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  73 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 58 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 73 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 73 145 (accept_3_3 56 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 73 145 (Polychromatic418967fa.accept_20_15_13_5_1_6061 55 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 73 145
  (Polychromatic418967fa.accept_14_12_3_5_1_1868 54 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 73 145 (accept_3_3 53 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  73 145 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 73 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 73 145 (accept_3_3 50 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 73 145 (Polychromatic418967fa.accept_13_10_8_2_1_3829 49 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 73 145
  (Polychromatic418967fa.accept_10_8_3_5_1_613 48 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 73 145 (accept_3_3 47 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  73 145 (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 73 145 (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 73 145 (accept_3_3 44 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 73 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 73 145
  (Polychromatic418967fa.accept_10_2_3_5_1_996 42 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 73 145 (accept_3_3 41 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  73 145 (Polychromatic418967fa.accept_14_12_3_5_1_1868 40 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 73 145 (Polychromatic418967fa.accept_20_19_13_5_1_7722 39 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 73 145 (accept_3_3 38 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 73 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 73 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 73 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 73 145 (accept_3_3 35 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  73 145 (Polychromatic418967fa.accept_15_4_13_10_1_1508 34 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 73 145 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 73 145 (accept_3_3 32 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 73 145 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 73 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 73 145 (accept_3_3 29 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  73 145 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 73 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 73 145 (accept_3_3 26 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 73 145 (Polychromatic418967fa.accept_19_6_16_12_1_6118 25 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 73 145
  (Polychromatic418967fa.accept_16_8_9_1_1_7753 24 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 73 145 (accept_3_3 23 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  73 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 73 145 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 73 145 (accept_3_3 20 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 73 145 (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 73 145
  (Polychromatic418967fa.accept_10_8_3_5_1_613 18 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 73 145 (accept_3_3 17 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  73 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 73 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 73 145 (accept_3_3 14 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 73 145 (Polychromatic418967fa.accept_16_13_9_1_1_3022 13 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 73 145
  (Polychromatic418967fa.accept_10_2_3_5_1_996 12 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 73 145 (accept_3_3 11 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  73 145 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 73 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 73 145 (accept_3_3 8 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 73 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 73 145
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 73 145 (accept_3_3 5 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 73
  145 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 73 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 73 145 (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 145 (accept_3_3 2 73 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 73 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 145 (allA_succ_of_accept 71
  72 145 (accept_3_3 71 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 72 145
  (Polychromatic418967fa.accept_11_4_6_2_1_51 70 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 72 145 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 72 145 (accept_3_3 68 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 72 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 67 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 72 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 66
  72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 72 145 (accept_3_3 65 72
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 72 145
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 64 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 72 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 72 145 (accept_3_3 62 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 72 145 (Polychromatic418967fa.accept_13_9_7_2_1_3869 61 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 72 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 60
  72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 72 145 (accept_3_3 59 72
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 72 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 58 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 72 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 57 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 72 145 (accept_3_3 56 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 72 145 (Polychromatic418967fa.accept_16_7_8_1_1_3061 55 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 72 145 (Polychromatic418967fa.accept_15_9_12_10_1_809
  54 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 72 145 (accept_3_3 53
  72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 72 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 72 145 (Polychromatic418967fa.accept_15_6_12_10_1_1543 51 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 72 145 (accept_3_3 50 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 72 145 (Polychromatic418967fa.accept_14_7_2_5_1_4528 49 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 72 145 (Polychromatic418967fa.accept_10_8_2_5_1_596
  48 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 72 145 (accept_3_3 47
  72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 72 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 46 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 72 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 72 145 (accept_3_3 44 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 72 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 43 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 72 145
  (Polychromatic418967fa.accept_22_20_6_13_1_7752 42 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 72 145 (accept_3_3 41 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  72 145 (Polychromatic418967fa.accept_22_18_6_13_1_7751 40 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 72 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 72 145 (accept_3_3 38 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 72 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 72 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 72 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 72 145 (accept_3_3 35 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  72 145 (Polychromatic418967fa.accept_13_8_7_2_1_2988 34 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 72 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 72 145 (accept_3_3 32 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 72 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 72 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 72 145
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 30 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 72 145 (accept_3_3 29 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  72 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 72 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 72 145 (accept_3_3 26 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 72 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 72 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 72 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 72 145 (accept_3_3 23 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  72 145 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 72 145 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 72 145 (accept_3_3 20 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 72 145 (Polychromatic418967fa.accept_17_2_4_9_1_2791 19 72 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 72 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 72 145 (accept_3_3 17 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  72 145 (Polychromatic418967fa.accept_19_16_15_12_1_2266 16 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 72 145 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 72 145 (accept_3_3 14 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 72 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 72 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 72 145
  (Polychromatic418967fa.accept_16_12_8_1_1_5270 12 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 72 145 (accept_3_3 11 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  72 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 72 145 (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 72 145 (accept_3_3 8 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 72 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 72 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 72 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 72 145 (accept_3_3 5 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 72
  145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 72 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 72 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 72 145 (accept_3_3 2 72 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 72 145 (Polychromatic418967fa.accept_27_1_18_10_1_7750 1 72 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 145 (allA_of_3_1 71 71 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 70 145 (allA_succ_of_accept 69 70 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 70 145 (accept_3_3 68 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  70 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 70 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 70 145 5 13 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 70 145
  (Polychromatic418967fa.accept_11_9_4_2_1_600 64 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 70 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 70 145 (accept_3_3 62 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 70 145 (Polychromatic418967fa.accept_11_6_4_2_1_599 61 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 145 5 12 14 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 145 (accept_3_3 59 70 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 70 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 70 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 70 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 70 145 (accept_3_3 56 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 70
  145 5 11 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54
  70 145 (Polychromatic418967fa.accept_19_16_13_12_1_7749 54 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 70 145 (accept_3_3 53 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 70 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 70 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 70 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 70 145 5 10 14 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 70 145
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 70 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 70 145 (accept_3_3 47 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 70 145 (Polychromatic418967fa.accept_13_7_5_2_1_401 46 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 70 145 5 9 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 70 145 (accept_3_3 44 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 70 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 70 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 70 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 70 145 (accept_3_3 41 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70
  145 5 8 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  70 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 70 145 (accept_3_3 38 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 70 145 (Polychromatic418967fa.accept_16_5_6_1_1_2118 37 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 70 145 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 70
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 70 145 5 7 14 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 70 145
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 34 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 70 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 70 145 (accept_3_3 32 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 70 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 145 5 6 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 145 (accept_3_3 29 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 70 145 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 70 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 70 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 70 145 (accept_3_3 26 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 70
  145 5 5 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  70 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 70 145 (accept_3_3 23 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 70 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 70 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 70 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 145 5 4 14 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 70 145 (Polychromatic418967fa.accept_16_2_6_1_1_2069 18 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 70 145 (accept_3_3 17 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 70 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 70 145 5 3 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 70 145 (accept_3_3 14 70 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 70 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 70 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 70 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 70 145 (accept_3_3 11 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70
  145 5 2 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  70 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 70 145 (accept_3_3 8 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 70
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 70 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 70 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 70 145 5 1 14 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 70 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 70 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 70 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 70 145 (accept_3_3 2 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 70
  145 (Polychromatic418967fa.accept_19_1_13_12_1_7748 1 70 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 70 145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 145
  (allA_succ_of_accept 68 69 145 (accept_3_3 68 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  69 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 67 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 69 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 69 145 (accept_3_3 65 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 145
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 69 145 (accept_3_3 62 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  69 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 69 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 69 145 (accept_3_3 59 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 145
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 69 145 (accept_3_3 56 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  69 145 (Polychromatic418967fa.accept_20_15_9_5_1_4684 55 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 69 145 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 145 (accept_3_3 53 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 145
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 69 145 (accept_3_3 50 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  69 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 69 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 69 145 (accept_3_3 47 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 145
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 69 145 (accept_3_3 44 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  69 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 69 145 (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 69 145 (accept_3_3 41 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 69 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 145
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 69 145 (accept_3_3 38 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  69 145 (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 69 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 69 145 (accept_3_3 35 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 145
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 69 145 (accept_3_3 32 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  69 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 69 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 69 145 (accept_3_3 29 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 145
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 69 145 (accept_3_3 26 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  69 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 69 145 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 69 145 (accept_3_3 23 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 69 145 (accept_3_3 20 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  69 145 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 69 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 69 145 (accept_3_3 17 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 145
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 69 145 (accept_3_3 14 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  69 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 69 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 69 145 (accept_3_3 11 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 69 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 145
  (Polychromatic418967fa.accept_16_9_5_1_1_1259 9 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 69 145 (accept_3_3 8 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69
  145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 69 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 69 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 69 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 69 145 (accept_3_3 5 69 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 69 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 69 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 69 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 69
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 145 (accept_3_3 2 69 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 69
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 145 (allA_of_3_1 68 68 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 67 145 (allA_succ_of_accept 66 67 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 67 145 (accept_3_3 65 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64
  67 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 64 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 67 145 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 67 145 (accept_3_3 62 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 67 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 67 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 67 145 (accept_3_3 59 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  67 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 67 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 67 145 (accept_3_3 56 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 67 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 55 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 67 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 67 145 (accept_3_3 53 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  67 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 67 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 67 145 (accept_3_3 50 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 67 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 67 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 67 145 (accept_3_3 47 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  67 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 67 145 (Polychromatic418967fa.accept_16_13_3_1_1_2100 45 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 67 145 (accept_3_3 44 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 67 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 67 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 67 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 67 145 (accept_3_3 41 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  67 145 (Polychromatic418967fa.accept_17_6_16_9_1_5129 40 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 67 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 67 145 (accept_3_3 38 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 67 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 67 145
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 67 145 (accept_3_3 35 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  67 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 67 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 67 145 (accept_3_3 32 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 67 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 67 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 67 145 (accept_3_3 29 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  67 145 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 67 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 67 145 (accept_3_3 26 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 67 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 67 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 67 145 (accept_3_3 23 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  67 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 67 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 67 145 (accept_3_3 20 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 67 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 67 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 67 145 (accept_3_3 17 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  67 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 67 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 67 145 (accept_3_3 14 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 67 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 67 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 67 145 (accept_3_3 11 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  67 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 67 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 67 145 (accept_3_3 8 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 67 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 67 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 67 145 (accept_3_3 5 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 67
  145 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 67 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 67 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 67 145 (accept_3_3 2 67 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 67 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 67 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 67
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 145 (allA_succ_of_accept 65 66
  145 (accept_3_3 65 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 66 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 64 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 66 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 66 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 66 145 (accept_3_3 62 66 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 66 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 66 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 60
  66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 66 145 (accept_3_3 59 66
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 66 145 (Polychromatic418967fa.accept_7_2_3_5_1_34
  58 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 66 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 66 145 (accept_3_3 56 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  66 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 66 145 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 66 145 (accept_3_3 53 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 66 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 66 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 66 145 (accept_3_3 50 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  66 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 66 145 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 66 145 (accept_3_3 47 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 66 145 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 66 145
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 45 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 66 145 (accept_3_3 44 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  66 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 66 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 66 145 (accept_3_3 41 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 66 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 66 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 66 145 (accept_3_3 38 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  66 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 66 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 66 145 (accept_3_3 35 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 66 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 66 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 66 145 (accept_3_3 32 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  66 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 66 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 66 145 (accept_3_3 29 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 66 145 (Polychromatic418967fa.accept_16_12_2_1_1_1215 28 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 66 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 66 145 (accept_3_3 26 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  66 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 66 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 66 145 (accept_3_3 23 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 66 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 66 145
  (Polychromatic418967fa.accept_10_1_6_5_1_304 21 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 66 145 (accept_3_3 20 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  66 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 66 145 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 66 145 (accept_3_3 17 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 66 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 66 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 66 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 66 145 (accept_3_3 14 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  66 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 66 145 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 66 145 (accept_3_3 11 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 66 145 (Polychromatic418967fa.accept_19_10_9_12_1_4774 10 66 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 66 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 66 145 (accept_3_3 8 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 66
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 66 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 66 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 66 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 66 145 (accept_3_3 5 66 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 66 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 66 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 66 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 66
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 66 145 (accept_3_3 2 66 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 66 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 66
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 145 (allA_of_3_1 65 65 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 64 145 (allA_succ_of_accept 63 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 64 145 (accept_3_3 62 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  64 145 (Polychromatic418967fa.accept_10_1_4_5_1_1031 61 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 64 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 64 145 (accept_3_3 59 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 64 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 64 145 (accept_3_3 56 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  64 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 64 145 (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 64 145 (accept_3_3 53 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 64 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 52 64 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 64 145 (accept_3_3 50 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  64 145 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 64 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 64 145 (accept_3_3 47 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 64 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 46 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 64 145 (accept_3_3 44 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  64 145 (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 64 145 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 64 145 (accept_3_3 41 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 64 145 (Polychromatic418967fa.accept_11_7_9_2_1_260 40 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 64 145 (accept_3_3 38 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  64 145 (Polychromatic418967fa.accept_11_4_9_2_1_259 37 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 64 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 64 145 (accept_3_3 35 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 64 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 64 145 (accept_3_3 32 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  64 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 64 145 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 64 145 (accept_3_3 29 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 64 145 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 64
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 64 145 (accept_3_3 26 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  64 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 64 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 64 145 (accept_3_3 23 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 64 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 64 145 (accept_3_3 20 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  64 145 (Polychromatic418967fa.accept_10_9_4_5_1_616 19 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 64 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 64 145 (accept_3_3 17 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 64 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 64 145 (accept_3_3 14 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  64 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 64 145 (Polychromatic418967fa.accept_21_12_1_19_1_4485 12 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 64 145 (accept_3_3 11 64 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 64 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 64 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 64 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 64 145 (accept_3_3 8 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 64
  145 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 64 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 64 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 64 145 (accept_3_3 5 64 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 64 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 64 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 64 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 64
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 64 145 (accept_3_3 2 64 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 64 145 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1
  64 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 64
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 145 (allA_succ_of_accept 62 63 145
  (accept_3_3 62 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 145
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 61 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 63 145 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 63 145 (accept_3_3 59 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 145 (Polychromatic418967fa.accept_10_7_3_5_1_301
  57 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 145 (accept_3_3 56
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 145
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 63 145 (accept_3_3 53 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 63 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 145 (Polychromatic418967fa.accept_14_9_7_5_1_1105
  51 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 145 (accept_3_3 50
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 63 145
  (Polychromatic418967fa.accept_11_5_8_2_1_588 49 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 63 145 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 145 (accept_3_3 47 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 145 (Polychromatic418967fa.accept_12_9_3_1_1_303
  45 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 145 (accept_3_3 44
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 145
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 63 145 (accept_3_3 41 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 63 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 145 (Polychromatic418967fa.accept_15_9_3_10_1_2312
  39 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 145 (accept_3_3 38
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 145
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 63 145 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 63 145 (accept_3_3 35 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 145 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 145 (accept_3_3 32
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 63 145
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 31 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 63 145 (accept_3_3 29 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 63 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 145 (Polychromatic418967fa.accept_10_7_3_5_1_301
  27 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 145 (accept_3_3 26
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 145
  (Polychromatic418967fa.accept_27_25_9_10_1_3770 25 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 63 145 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 63 145 (accept_3_3 23 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 145 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 145 (accept_3_3 20
  63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 145
  (Polychromatic418967fa.accept_27_19_9_10_1_7747 19 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 63 145 (accept_3_3 17 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 63 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 145
  (Polychromatic418967fa.accept_19_15_6_12_1_7746 15 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 63 145 (accept_3_3 14 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  63 145 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 63 145 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 63 145 (accept_3_3 11 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 63 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 63 145 (accept_3_3 8 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63
  145 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 63 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 63 145 (accept_3_3 5 63 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 63 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 63 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 145 (Polychromatic418967fa.accept_13_3_11_2_1_1422
  3 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 145 (accept_3_3 2 63
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 145
  (Polychromatic418967fa.accept_20_1_3_5_1_1060 1 63 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 145 (allA_of_3_1 62 62
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 61 145 (allA_succ_of_accept 60 61 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 60 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 145 (accept_3_3 59 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 145 (accept_3_3 56 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 145 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 145
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 145 (accept_3_3 53 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 145 (accept_3_3 50 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 145 (accept_3_3 47 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 145 (Polychromatic418967fa.accept_10_6_1_5_1_1024 46 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 145 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 145 (accept_3_3 44 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 61 145 (accept_3_3 41 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  61 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 61 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 145 (accept_3_3 38 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 145 (Polychromatic418967fa.accept_11_4_6_2_1_51 37 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 145 (accept_3_3 35 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 145 (Polychromatic418967fa.accept_10_4_1_5_1_1018 34 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 145 (accept_3_3 32 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 145 (accept_3_3 29 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 145 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 145 (accept_3_3 26 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 145 (Polychromatic418967fa.accept_16_9_13_1_1_3069 25 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 145 (accept_3_3 23 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 145 (accept_3_3 20 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 145
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 145 (accept_3_3 17 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 145 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 145 (accept_3_3 14 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 145 (accept_3_3 11 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 145 (Polychromatic418967fa.accept_20_10_1_5_1_7745 10 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 145 (accept_3_3 8 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 145 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 61 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 145 (accept_3_3 5 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  145 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 61 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 61 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 61 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 145 (accept_3_3 2 61 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 61 145 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 61 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61 145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 60 145 (allA_succ_of_accept 59 60 145 (accept_3_3 59 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 60 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 58 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 60 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 60 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 60 145 (accept_3_3 56 60 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 60 145 5 11 12 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 60 145
  (Polychromatic418967fa.accept_21_12_18_19_1_7744 54 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 60 145 (accept_3_3 53 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 60 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 60 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 60 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 60 145 5 10 12 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 145
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 60 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 60 145 (accept_3_3 47 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 60 145 (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 60 145 5 9 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 60 145 (accept_3_3 44 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 60 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 43 60 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 60 145
  (Polychromatic418967fa.accept_23_19_14_7_1_7743 42 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 60 145 (accept_3_3 41 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 60
  145 5 8 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  60 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 60 145 (accept_3_3 38 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 60 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 60 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 60 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 60 145 5 7 12 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 60 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 34 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 60 145 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 60 145 (accept_3_3 32 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 60 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 145 5 6 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 145 (accept_3_3 29 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 60 145 (Polychromatic418967fa.accept_19_9_3_12_1_6191 28 60 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 60 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 60 145 (accept_3_3 26 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 60
  145 5 5 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  60 145 (Polychromatic418967fa.accept_16_8_12_1_1_7720 24 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 60 145 (accept_3_3 23 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 60 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 60 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 60 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 145 5 4 12 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 145
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 60 145 (Polychromatic418967fa.accept_16_2_12_1_1_3086 18 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 60 145 (accept_3_3 17 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 60 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 60 145 5 3 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 60 145 (accept_3_3 14 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 60 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 60 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 60 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 60 145 (accept_3_3 11 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60
  145 5 2 12 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  60 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 60 145 (accept_3_3 8 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 60 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 60 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 60 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 60 145 5 1 12 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 60 145
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 60 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 60 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 60 145 (accept_3_3 2 60 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 60 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 60 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60 145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 59 145 (allA_of_3_1 59 59 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 58 145
  (allA_succ_of_accept 57 58 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 58 145 (accept_3_3 56 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 58 145 (Polychromatic418967fa.accept_28_26_2_5_1_7742
  54 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 58 145 (accept_3_3 53
  58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 58 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 52 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 58 145 (accept_3_3 50 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 58 145 (Polychromatic418967fa.accept_13_10_6_2_1_1440 49 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 58 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 58 145 (accept_3_3 47 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  58 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 46 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 58 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 58 145 (accept_3_3 44 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 58 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 58 145 (accept_3_3 41 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  58 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 58 145 (accept_3_3 38 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 58 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 58 145
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 58 145 (accept_3_3 35 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  58 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 58 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 58 145 (accept_3_3 32 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 58 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 29 58 145 29 1 2 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 28 58 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 58 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 58 145 (accept_3_3 26 58 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 58 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25
  58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 58 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 58 145 (accept_3_3 23 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  58 145 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 58 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 58 145 (accept_3_3 20 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 58 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 58 145 (accept_3_3 17 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  58 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 58 145 (accept_3_3 14 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 58 145 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 58 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 58 145 (accept_3_3 11 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  58 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 58 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 58 145 (accept_3_3 8 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 58 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 58 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 58 145 (accept_3_3 5 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 58
  145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 58 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 58 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 58 145 (accept_3_3 2 58 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 58 145 (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 58 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 58 145))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 57 145 (allA_succ_of_accept 56 57 145 (accept_3_3 56 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 55 57 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 57 145 (Polychromatic418967fa.accept_15_9_12_10_1_809 54 57
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 57 145 (accept_3_3 53 57 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 52
  57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 57 145 (accept_3_3 50 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  57 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 57 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 57 145 (accept_3_3 47 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 57 145 (accept_3_3 44 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  57 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 57 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 57 145 (accept_3_3 41 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 145
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 57 145 (accept_3_3 38 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  57 145 (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 57 145 (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 57 145 (accept_3_3 35 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 57 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 57 145 (accept_3_3 32 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  57 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 57 145 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 57 145 (accept_3_3 29 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 145
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 57 145 (accept_3_3 26 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  57 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 57 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 57 145 (accept_3_3 23 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 57 145 (accept_3_3 20 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  57 145 (Polychromatic418967fa.accept_23_19_11_7_1_7741 19 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 57 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 57 145 (accept_3_3 17 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 57 145 (accept_3_3 14 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  57 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 57 145 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 57 145 (accept_3_3 11 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 57 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 145
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 57 145 (accept_3_3 8 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 57
  145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 57 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 57 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 57 145 (accept_3_3 5 57 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 57 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 57 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 57 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 57
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 145 (accept_3_3 2 57 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 145 (Polychromatic418967fa.accept_21_1_15_19_1_4491
  1 57 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  145))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 145 (allA_of_3_1 56 56 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 55 145 (allA_succ_of_accept 54 55 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 145 (accept_3_3 53 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 145 (Polychromatic418967fa.accept_19_14_17_12_1_6099 52 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 145 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 55 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 55 145 5 10 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 55 145
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 55 145 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 55 145 (accept_3_3 47 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 55 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 55 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 55 145 5 9 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 55 145 (accept_3_3 44 55 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 55 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 145 (accept_3_3 41 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 55
  145 5 8 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  55 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 55 145 (accept_3_3 38 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 55 145 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 55 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 55 145 5 7 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 55 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 55 145 (Polychromatic418967fa.accept_19_14_17_12_1_6099 33 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 145 (accept_3_3 32 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 55 145 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 55 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 55 145 5 6 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 55 145 (accept_3_3 29 55 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 55 145 (Polychromatic418967fa.accept_20_8_15_5_1_2096 28 55 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 55 145
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 55 145 (accept_3_3 26 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 55
  145 5 5 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  55 145 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 55 145 (accept_3_3 23 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 55 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 55 145 (Polychromatic418967fa.accept_19_2_17_12_1_6097 21 55
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 55 145 5 4 11 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 55 145
  (Polychromatic418967fa.accept_17_2_4_9_1_2791 19 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 55 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 55 145 (accept_3_3 17 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 55 145 (Polychromatic418967fa.accept_20_16_15_5_1_7740 16 55 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 55 145 5 3 11 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 55 145 (accept_3_3 14 55 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 145 (Polychromatic418967fa.accept_17_13_4_9_1_6390 13 55
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 145
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 145 (accept_3_3 11 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 55
  145 5 2 11 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  55 145 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 55 145 (accept_3_3 8 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 55 145 (Polychromatic418967fa.accept_20_7_15_5_1_6087 7 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 55 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 55 145 5 1 11 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 55 145
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 55 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 55 145 (Polychromatic418967fa.accept_19_3_17_12_1_6176 3 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 145 (accept_3_3 2 55 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 55 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 55 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55 145)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 54 145 (allA_succ_of_accept 53 54 145 (accept_3_3 53 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 54 145 (Polychromatic418967fa.accept_14_10_12_5_1_3466 52 54 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 54 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 54 145 (accept_3_3 50 54 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 54 145 (Polychromatic418967fa.accept_10_9_4_5_1_616
  49 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 54 145
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 48 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 54 145 (accept_3_3 47 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  54 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 54 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 54 145 (accept_3_3 44 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 54 145
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 54 145 (accept_3_3 41 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  54 145 (Polychromatic418967fa.accept_17_6_3_9_1_7739 40 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 54 145 (accept_3_3 38 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 54 145 (Polychromatic418967fa.accept_16_5_6_1_1_2118 37 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 54 145
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 54 145 (accept_3_3 35 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  54 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 54 145 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 54 145 (accept_3_3 32 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 54 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 54 145
  (Polychromatic418967fa.accept_20_10_14_5_1_3331 30 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 54 145 (accept_3_3 29 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  54 145 (Polychromatic418967fa.accept_17_11_3_9_1_6387 28 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 54 145 (accept_3_3 26 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 54 145 (Polychromatic418967fa.accept_19_6_16_12_1_6118 25 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 54 145
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 24 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 54 145 (accept_3_3 23 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  54 145 (Polychromatic418967fa.accept_21_1_12_19_1_7721 22 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 54 145 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 54 145 (accept_3_3 20 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 54 145
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 54 145 (accept_3_3 17 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  54 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 54 145 (accept_3_3 14 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 54 145 (Polychromatic418967fa.accept_19_13_16_12_1_6096 13 54 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 54 145
  (Polychromatic418967fa.accept_11_1_10_2_1_58 12 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 54 145 (accept_3_3 11 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  54 145 (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 54 145 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 54 145 (accept_3_3 8 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 54 145
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 54 145 (accept_3_3 5 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 54
  145 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 54 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 54 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 54 145 (accept_3_3 2 54 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 54 145 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 54 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 145 (allA_of_3_1 53 53 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 52 145 (allA_succ_of_accept 51 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 52
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 52 145 (accept_3_3 50 52 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 52 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 49
  52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 52 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 52 145 (accept_3_3 47 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  52 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 52 145 (accept_3_3 44 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 52 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 43 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 52 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 52 145 (accept_3_3 41 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  52 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 52 145 (accept_3_3 38 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 52 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 52 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 36 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 52 145 (accept_3_3 35 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  52 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 52 145 (accept_3_3 32 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 52 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 52 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 30 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 52 145 (accept_3_3 29 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  52 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 52 145 (accept_3_3 26 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 52 145 (Polychromatic418967fa.accept_17_8_1_9_1_7738 25 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 52 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 52 145 (accept_3_3 23 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  52 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 52 145 (accept_3_3 20 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 52 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 52 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 52 145 (accept_3_3 17 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  52 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 52 145 (accept_3_3 14 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 52 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 52 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 52 145 (accept_3_3 11 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  52 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 52 145 (accept_3_3 8 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 52 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 52 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 52 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 52 145 (accept_3_3 5 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 52
  145 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 52 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 52 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 52 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 52 145 (accept_3_3 2 52 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 52 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 52 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 52 145))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 51 145 (allA_succ_of_accept 50 51 145 (accept_3_3 50 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 51 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 51 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 51 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 145 (accept_3_3 47 51 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 145 (accept_3_3 44 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  51 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 145 (accept_3_3 41 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 51 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 145 (accept_3_3 38 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  51 145 (Polychromatic418967fa.accept_19_18_13_12_1_4775 37 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 145 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 145 (accept_3_3 35 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 51 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 145 (accept_3_3 32 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  51 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 145 (accept_3_3 29 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 51 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 145
  (Polychromatic418967fa.accept_13_1_12_2_1_384 27 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 145 (accept_3_3 26 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  51 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 145 (accept_3_3 23 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 51 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 51 145 (accept_3_3 20 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  51 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 145 (accept_3_3 17 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 51 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 145
  (Polychromatic418967fa.accept_20_15_11_5_1_7737 15 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 51 145 (accept_3_3 14 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  51 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 51 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 145 (accept_3_3 11 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 51 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 145
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 51 145 (accept_3_3 8 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51
  145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 51 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 51 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 145 (accept_3_3 5 51 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 51 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 51 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3
  51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 145 (accept_3_3 2 51 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 145 (Polychromatic418967fa.accept_13_1_12_2_1_384 1
  51 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51
  145))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 145 (allA_of_3_1 50 50 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 49 145 (allA_succ_of_accept 48 49 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 49
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 49 145 (accept_3_3 47 49 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 49 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046
  46 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 145
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 49 145 (accept_3_3 44 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  49 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 49 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 49 145 (accept_3_3 41 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 49 145 (Polychromatic418967fa.accept_14_12_7_5_1_1107 40 49 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 49 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 49 145 (accept_3_3 38 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  49 145 (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 49 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 49 145 (accept_3_3 35 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 49 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 49 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 49 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 49 145 (accept_3_3 32 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  49 145 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 49 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 49 145 (accept_3_3 29 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 49 145 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 49 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 49 145
  (Polychromatic418967fa.accept_19_8_11_12_1_6165 27 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 49 145 (accept_3_3 26 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  49 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 49 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 49 145 (accept_3_3 23 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 49 145 (Polychromatic418967fa.accept_15_7_4_10_1_1513 22 49 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 49 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 49 145 (accept_3_3 20 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  49 145 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 49 145 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 49 145 (accept_3_3 17 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 49 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 49 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 49 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 49 145 (accept_3_3 14 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  49 145 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 49 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 49 145 (accept_3_3 11 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 49 145 (Polychromatic418967fa.accept_18_10_13_1_1_7736 10 49 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 49 145
  (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 49 145 (accept_3_3 8 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 49
  145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 49 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 49 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 49 145 (accept_3_3 5 49 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 49 145 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 49 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 49 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 49
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 145 (accept_3_3 2 49 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 145 (Polychromatic418967fa.accept_10_1_9_5_1_83 1
  49 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49
  145))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 48 145 (allA_succ_of_accept 47 48 145 (accept_3_3 47
  48 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 48 145
  (Polychromatic418967fa.accept_7_4_6_5_1_141 46 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 48 145 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 48 145 (accept_3_3 44 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 48 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 43 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 48 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 42
  48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 48 145 (accept_3_3 41 48
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 48 145
  (Polychromatic418967fa.accept_9_4_3_1_1_154 40 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 48 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 48 145 (accept_3_3 38 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 48 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 37 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 48 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 36
  48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 48 145 (accept_3_3 35 48
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 48 145
  (Polychromatic418967fa.accept_9_7_3_1_1_386 34 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 48 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 48 145 (accept_3_3 32 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 48 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 48 145
  (Polychromatic418967fa.accept_19_11_10_12_1_2256 30 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 48 145 (accept_3_3 29 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 48 145 (Polychromatic418967fa.accept_11_6_4_2_1_599 28 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 48 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 48 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 48 145 (accept_3_3 26 48 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 48 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25
  48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 48 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 48 145 (accept_3_3 23 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  48 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 48 145 (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 48 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 48 145 (accept_3_3 20 48 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 48 145 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 48 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 48 145
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 48 145 (accept_3_3 17 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  48 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 48 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 48 145 (accept_3_3 14 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 48 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 48 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 48 145
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 48 145 (accept_3_3 11 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  48 145 (Polychromatic418967fa.accept_20_10_8_5_1_7735 10 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 48 145 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 48 145 (accept_3_3 8 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 48 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 48 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 48 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 48 145 (accept_3_3 5 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 48
  145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 48 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 48 145 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 48 145 (accept_3_3 2 48 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 48 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 48 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48 145)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  47 145 (allA_of_3_1 47 47 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 46 145 (allA_succ_of_accept 45 46
  145 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 46 145 (accept_3_3 44 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  46 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 46 145 (Polychromatic418967fa.accept_19_4_8_12_1_4757 42 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 46 145 (accept_3_3 41 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 46 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 46 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 46 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 46 145 (accept_3_3 38 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  46 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 37 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 46 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 46 145 (accept_3_3 35 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 46 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 34 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 46 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 46 145 (accept_3_3 32 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  46 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 46 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 46 145 (accept_3_3 29 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 46 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 46 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 46 145 (accept_3_3 26 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  46 145 (Polychromatic418967fa.accept_19_6_8_12_1_6271 25 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 46 145 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 46 145 (accept_3_3 23 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 46 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 22 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 46 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 46 145 (accept_3_3 20 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  46 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 46 145 (Polychromatic418967fa.accept_13_5_7_2_1_852 18 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 46 145 (accept_3_3 17 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 46 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 16 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 46 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 46 145 (accept_3_3 14 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  46 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 46 145 (Polychromatic418967fa.accept_20_12_6_5_1_7734 12 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 46 145 (accept_3_3 11 46 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 46 145 (Polychromatic418967fa.accept_19_10_8_12_1_7733 10 46
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 46 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 46 145 (accept_3_3 8 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 46
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 46 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 46 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 46 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 46 145 (accept_3_3 5 46 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 46 145 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 46 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 46 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 46
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 46 145 (accept_3_3 2 46 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 46 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 46
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  145)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 145 (allA_succ_of_accept 44 45 145 (accept_3_3 44 45
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 145 (Polychromatic418967fa.accept_7_1_3_5_1_33
  43 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 145
  (Polychromatic418967fa.accept_17_8_11_9_1_5099 42 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 145 (accept_3_3 41 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 45
  145 5 8 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  45 145 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 145 (accept_3_3 38 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 45 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 37 45 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 45 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 45 145 5 7 9 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 45 145
  (Polychromatic418967fa.accept_6_4_3_1_1_57 34 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 45 145 (Polychromatic418967fa.accept_19_14_7_12_1_7732 33 45 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 145 (accept_3_3 32 45 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 45 145 (Polychromatic418967fa.accept_22_9_1_13_1_7731 31 45 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 45 145 5 6 9 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 45 145 (accept_3_3 29 45 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 45 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 145
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 45 145 (accept_3_3 26 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 45
  145 5 5 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24
  45 145 (Polychromatic418967fa.accept_18_6_9_1_1_3769 24 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 145 (accept_3_3 23 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 45 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 145 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 45
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 45 145 5 4 9 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 45 145
  (Polychromatic418967fa.accept_16_3_13_1_1_1206 19 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 45 145 (Polychromatic418967fa.accept_19_18_7_12_1_6148 18 45 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 145 (accept_3_3 17 45 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 45 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 45 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 145 5 3 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 145 (accept_3_3 14 45 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 145 (Polychromatic418967fa.accept_24_13_21_1_1_7730 13 45 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 45 145 (accept_3_3 11 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 45
  145 5 2 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 45
  145 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 145 (accept_3_3 8 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45
  145 (Polychromatic418967fa.accept_26_7_19_15_1_7729 7 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 145 (Polychromatic418967fa.accept_18_6_9_1_1_3769 6 45 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 45 145 5 1 9 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 45 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 45
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 145
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 45 145 (accept_3_3 2 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45
  145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 45 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 45 145))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 145 (allA_of_3_1 44 44 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 43 145 (allA_succ_of_accept 42 43 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 43 145 (accept_3_3 41 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  43 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 43 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 145 (accept_3_3 38 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 43 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 145
  (Polychromatic418967fa.accept_19_17_5_12_1_4753 36 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 145 (accept_3_3 35 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 145 (accept_3_3 32 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 43 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 145 (accept_3_3 29 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 145 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 145 (accept_3_3 26 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 43 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 145 (accept_3_3 23 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 145 (accept_3_3 20 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 145 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 43 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 145 (accept_3_3 17 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 145 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 145 (accept_3_3 14 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 43 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 145 (accept_3_3 11 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 145 (Polychromatic418967fa.accept_19_9_5_12_1_7728 9 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 145 (accept_3_3 8 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 145 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 43 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 145 (accept_3_3 5 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 43 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 43 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 43 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 145 (accept_3_3 2 43 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 43 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 43 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 145))))))))))))))))))))))))))))))))))))))))))) (allB_succ 42 145
  (allA_succ_of_accept 41 42 145 (accept_3_3 41 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  42 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 42 145 (accept_3_3 38 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 42 145 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 42 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 42 145
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 42 145 (accept_3_3 35 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  42 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 42 145 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 42 145 (accept_3_3 32 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 42 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 42 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 42 145 (accept_3_3 29 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  42 145 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 42 145 (accept_3_3 26 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 42 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 42 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 42 145
  (Polychromatic418967fa.accept_13_11_3_2_1_863 24 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 42 145 (accept_3_3 23 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  42 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 42 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 42 145 (accept_3_3 20 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 42 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 42 145
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 42 145 (accept_3_3 17 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  42 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 42 145 (accept_3_3 14 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 42 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 42 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 42 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 42 145 (accept_3_3 11 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  42 145 (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 42 145 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 42 145 (accept_3_3 8 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 42 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 42 145
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 6 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 42 145 (accept_3_3 5 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 42
  145 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 42 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 42 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 42 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 42 145 (accept_3_3 2 42 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 42 145 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 42 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42 145)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 145
  (allA_of_3_1 41 41 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 40 145 (allA_succ_of_accept 39 40 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 40 145 (accept_3_3 38 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  40 145 (Polychromatic418967fa.accept_17_3_6_9_1_2761 37 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 40 145 (Polychromatic418967fa.accept_16_4_8_1_1_5257 36 40 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 40 145 5 7 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 40 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 34
  40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 40 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 40 145 (accept_3_3 32 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  40 145 (Polychromatic418967fa.accept_11_9_7_2_1_1068 31 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 40 145 5 6 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 40 145 (accept_3_3 29 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 40 145 (Polychromatic418967fa.accept_16_12_8_1_1_5270 28 40 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 40 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 40 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 40 145 (accept_3_3 26 40 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 40 145 5 5 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 40 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 24
  40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 40 145 (accept_3_3 23 40
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 40 145
  (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 40 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 40 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 145 5 4 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 145 (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 40 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 40 145
  (Polychromatic418967fa.accept_25_18_15_20_1_7727 18 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 40 145 (accept_3_3 17 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 40 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 40 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 40 145 5 3 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 40 145 (accept_3_3 14 40 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 40 145 (Polychromatic418967fa.accept_23_13_17_7_1_7726 13 40 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 40 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 40 145 (accept_3_3 11 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40
  145 5 2 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 40
  145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 40 145 (accept_3_3 8 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 40
  145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 40 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 40 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 40 145 5 1 8 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 40 145 (Polychromatic418967fa.accept_16_4_8_1_1_5257 4 40 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 40 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 40 145 (accept_3_3 2 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 40
  145 (Polychromatic418967fa.accept_19_1_2_12_1_7725 1 40 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 40 145)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 145 (allA_succ_of_accept 38 39 145
  (accept_3_3 38 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 145
  (Polychromatic418967fa.accept_7_2_4_5_1_313 37 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 39 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 39 145 (accept_3_3 35 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 39 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 39 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 33
  39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 145 (accept_3_3 32 39
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 145
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 39 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 39 145 (accept_3_3 29 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 39 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 39 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 27
  39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 145 (accept_3_3 26 39
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 39 145
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 39 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 39 145 (accept_3_3 23 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 39 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 39 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 145 (Polychromatic418967fa.accept_10_1_9_5_1_83 21
  39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 145 (accept_3_3 20 39
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 145
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 39 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 39 145 (accept_3_3 17 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 39 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 39 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 15
  39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 145 (accept_3_3 14 39
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 39 145 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 39 145 (accept_3_3 11 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 39 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 39 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9
  39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 145 (accept_3_3 8 39 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 39 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7
  39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 145 (accept_3_3 5 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39
  145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 39 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 39 145 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 145 (accept_3_3 2 39 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 39 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 39 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 145))))))))))))))))))))))))))))))))))))))) (allB_succ 38 145
  (allA_of_3_1 38 38 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 37 145 (allA_succ_of_accept 36 37 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 37 145 (accept_3_3 35 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  37 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 34 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 37 145 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 145 (accept_3_3 32 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 31 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 145
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 145 (accept_3_3 29 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 145 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 145 (accept_3_3 26 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 25 37 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 145
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 145 (accept_3_3 23 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 145 (Polychromatic418967fa.accept_10_2_7_5_1_605 22 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 145 (Polychromatic418967fa.accept_14_7_9_5_1_529 21 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 145 (accept_3_3 20 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 145 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 37 145 (accept_3_3 17 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  37 145 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 37 145 (Polychromatic418967fa.accept_16_15_5_1_1_7724 15 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 145 (accept_3_3 14 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 145 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 37 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 145 (accept_3_3 11 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 145 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 145 (accept_3_3 8 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 145 (Polychromatic418967fa.accept_14_7_9_5_1_529 7 37 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 145
  (Polychromatic418967fa.accept_11_6_4_2_1_599 6 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 145 (accept_3_3 5 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 37 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 37 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 37 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 145 (accept_3_3 2 37 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 37 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 37 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 145))))))))))))))))))))))))))))))))))))) (allB_succ 36 145
  (allA_succ_of_accept 35 36 145 (accept_3_3 35 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  36 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 34 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 36 145 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 36 145 (accept_3_3 32 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 36 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 31 36 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 36 145
  (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 36 145 (accept_3_3 29 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  36 145 (Polychromatic418967fa.accept_16_12_4_1_1_1257 28 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 36 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 36 145 (accept_3_3 26 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 36 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 25 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 36 145
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 36 145 (accept_3_3 23 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  36 145 (Polychromatic418967fa.accept_19_3_17_12_1_6176 22 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 36 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 36 145 (accept_3_3 20 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 36 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 36 145
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 36 145 (accept_3_3 17 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  36 145 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 36 145 (Polychromatic418967fa.accept_19_15_17_12_1_7723 15 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 36 145 (accept_3_3 14 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 36 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 36 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 36 145
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 12 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 36 145 (accept_3_3 11 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  36 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 36 145 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 36 145 (accept_3_3 8 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 36 145 (Polychromatic418967fa.accept_17_7_2_9_1_6396 7 36 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 36 145
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 36 145 (accept_3_3 5 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 36
  145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 36 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 36 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 36 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 36 145 (accept_3_3 2 36 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 36 145 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 36 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36 145)))))))))))))))))))))))))))))))))))) (allB_succ 35 145
  (allA_of_3_1 35 35 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 34 145 (allA_succ_of_accept 33 34 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 34 145 (accept_3_3 32 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  34 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 34 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 34 145 (accept_3_3 29 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 34 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 34 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 34 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 34 145 (accept_3_3 26 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  34 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 34 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 34 145 (accept_3_3 23 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 34 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 22 34 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 34 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 34 145 (accept_3_3 20 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  34 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 34 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 34 145 (accept_3_3 17 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 34 145 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 34 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 34 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 34 145 (accept_3_3 14 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  34 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 34 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 34 145 (accept_3_3 11 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 34 145 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 34 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 34 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 34 145 (accept_3_3 8 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 34
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 34 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 34 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 34 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 34 145 (accept_3_3 5 34 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 34 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 34 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 34 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 34
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 34 145 (accept_3_3 2 34 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 34 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 34
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 34 145))))))))))))))))))))))))))))))))))
  (allB_succ 33 145 (allA_succ_of_accept 32 33 145 (accept_3_3 32 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 33 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 33 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 33 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 33 145 (accept_3_3 29 33 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 145
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 33 145 (accept_3_3 26 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  33 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 33 145 (Polychromatic418967fa.accept_15_9_3_10_1_2312 24 33 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 33 145 (accept_3_3 23 33 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 33 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 33 145 (accept_3_3 20 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  33 145 (Polychromatic418967fa.accept_20_19_13_5_1_7722 19 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 33 145 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 33 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 33 145 (accept_3_3 17 33 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 33 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 145
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 33 145 (accept_3_3 14 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  33 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 33 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 33 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 33 145 (accept_3_3 11 33 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 33 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 145
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 33 145 (accept_3_3 8 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33
  145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 33 145 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 33 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 33 145 (accept_3_3 5 33 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 33 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 33 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 33 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 33
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 145 (accept_3_3 2 33 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 145 (Polychromatic418967fa.accept_21_1_12_19_1_7721
  1 33 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33
  145))))))))))))))))))))))))))))))))) (allB_succ 32 145 (allA_of_3_1 32 32 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 31 145 (allA_succ_of_accept 30 31 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 31 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 31 145 (accept_3_3 29 31 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 31 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 31
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 31 145
  (Polychromatic418967fa.accept_16_11_15_1_1_2074 27 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 31 145 (accept_3_3 26 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  31 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 31 145 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 31 145 (accept_3_3 23 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 31 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 31 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 31 145
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 31 145 (accept_3_3 20 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  31 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 31 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 31 145 (accept_3_3 17 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 31 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 31 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 145
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 31 145 (accept_3_3 14 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  31 145 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 31 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 31 145 (accept_3_3 11 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 31 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 31 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 31 145
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 31 145 (accept_3_3 8 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 31
  145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 31 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 31 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 31 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 31 145 (accept_3_3 5 31 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 31 145 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 31 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 31 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 31
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 145 (accept_3_3 2 31 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 31 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 31
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 145)))))))))))))))))))))))))))))))
  (allB_succ 30 145 (allA_succ_of_accept 29 30 145 (accept_3_3 29 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 30 145 (Polychromatic418967fa.accept_20_8_10_5_1_6083 28 30 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 30 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 30 145 (accept_3_3 26 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 30 145 5 5 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 30 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 24
  30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 30 145 (accept_3_3 23 30
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 30 145
  (Polychromatic418967fa.accept_9_4_3_1_1_154 22 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 30 145 (Polychromatic418967fa.accept_14_7_2_5_1_4528 21 30 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 145 5 4 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 30 145
  (Polychromatic418967fa.accept_7_4_2_5_1_527 18 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 30 145 (accept_3_3 17 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  30 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 30 145 5 3 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 30 145 (accept_3_3 14 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 30 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 30 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 30 145 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 30
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 30 145 (accept_3_3 11 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 145 5 2 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 145 (Polychromatic418967fa.accept_20_9_10_5_1_6085 9
  30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 30 145 (accept_3_3 8 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 30 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 30
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 30 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 30 145 5 1 6 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 30 145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 30 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 30 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 30 145 (accept_3_3 2 30 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 30 145 (Polychromatic418967fa.accept_19_1_11_12_1_6112
  1 30 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30 145))))))))))))))))))))))))))))))
  (allB_succ 29 145 (allA_of_3_1 29 29 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 28 145
  (allA_succ_of_accept 27 28 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 28 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 28 145 (accept_3_3 26 28 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 28 145 (Polychromatic418967fa.accept_17_8_11_9_1_5099 25 28 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 28 145
  (Polychromatic418967fa.accept_16_8_12_1_1_7720 24 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 28 145 (accept_3_3 23 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  28 145 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 28 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 28 145 (accept_3_3 20 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 28 145 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 28 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 28 145
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 28 145 (accept_3_3 17 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  28 145 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 28 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 28 145 (accept_3_3 14 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 28 145 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 28 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 28 145
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 28 145 (accept_3_3 11 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  28 145 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 28 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 28 145 (accept_3_3 8 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 28 145 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 28 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 28 145
  (Polychromatic418967fa.accept_23_6_5_7_1_7719 6 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 28 145 (accept_3_3 5 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 28
  145 (Polychromatic418967fa.accept_11_4_6_2_1_51 4 28 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 28 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 28 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 28 145 (accept_3_3 2 28 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 28 145 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 28 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 28 145)))))))))))))))))))))))))))) (allB_succ 27 145
  (allA_succ_of_accept 26 27 145 (accept_3_3 26 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  27 145 (Polychromatic418967fa.accept_7_4_6_5_1_141 25 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 27 145 (Polychromatic418967fa.accept_15_9_12_10_1_809 24 27 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 145 (accept_3_3 23 27 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 27 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 27 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 27 145 (accept_3_3 20 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  27 145 (Polychromatic418967fa.accept_11_8_5_2_1_1629 19 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 27 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 27 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 145 (accept_3_3 17 27 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 27 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 27 145
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 27 145 (accept_3_3 14 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  27 145 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 27 145 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 27 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 145 (accept_3_3 11 27 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 27 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 145
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 145 (accept_3_3 8 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27
  145 (Polychromatic418967fa.accept_15_7_12_10_1_4335 7 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 27 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 145 (accept_3_3 5 27 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 27 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 145
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 27 145 (accept_3_3 2 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27
  145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 27 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 145))))))))))))))))))))))))))) (allB_succ 26 145 (allA_of_3_1 26 26 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 25 145 (allA_succ_of_accept 24 25 145 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 25 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 25 145 (accept_3_3 23 25 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 25 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 22
  25 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 25 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 25 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 25 145 5 4 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 25 145 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 25 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 145 (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 25
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 25 145 (accept_3_3 17 25 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 25 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 16
  25 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 25 145 5 3 5 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 25 145 (accept_3_3 14
  25 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 13 25 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 25 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 25 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 25 145 (accept_3_3 11 25 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 25 145 5 2 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 25 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 25 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 145 (accept_3_3 8 25 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 145 (Polychromatic418967fa.accept_21_7_4_19_1_4525 7 25 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 145
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 25 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 25 145 5 1 5 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 25 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 25 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 25 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 25 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 145 (accept_3_3 2 25 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 25
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 145))))))))))))))))))))))))) (allB_succ
  24 145 (allA_succ_of_accept 23 24 145 (accept_3_3 23 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 24 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 24 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 24 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 24 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 24 145 (accept_3_3 20 24 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 24 145 (Polychromatic418967fa.accept_10_9_4_5_1_616
  19 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 24 145
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 24 145 (accept_3_3 17 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  24 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 24 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 24 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 24 145 (accept_3_3 14 24 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 24 145 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 24 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 24 145
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 24 145 (accept_3_3 11 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  24 145 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 24 145 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 24 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 24 145 (accept_3_3 8 24 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 24 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 24 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 24 145
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 24 145 (accept_3_3 5 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 24
  145 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 24 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 24 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 24 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 24 145 (accept_3_3 2 24 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 24 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 24 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 145)))))))))))))))))))))))) (allB_succ 23 145 (allA_of_3_1 23 23
  145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 22 145 (allA_succ_of_accept 21 22 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 22 145 (accept_3_3 20 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  22 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 22 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 22 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 22 145 (accept_3_3 17 22 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 22 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 22 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 22 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 22 145 (accept_3_3 14 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  22 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 22 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 22 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 22 145 (accept_3_3 11 22 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 22 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 10 22 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 22 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 22 145 (accept_3_3 8 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 22
  145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 22 145 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 22 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 22 145 (accept_3_3 5 22 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 22 145 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 22 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 22 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 22
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 22 145 (accept_3_3 2 22 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 22 145 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1
  22 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 145)))))))))))))))))))))) (allB_succ
  21 145 (allA_succ_of_accept 20 21 145 (accept_3_3 20 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 145 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 21 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 145 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 21
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 21 145 (accept_3_3 17 21 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 16
  21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 145
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 21 145 (accept_3_3 14 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  21 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 21 145 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 21 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 21 145 (accept_3_3 11 21 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 21 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 145
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 21 145 (accept_3_3 8 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21
  145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 21 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 21 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 145 (accept_3_3 5 21 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 21 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 21 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21 145 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 145 (accept_3_3 2 21 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 145 (Polychromatic418967fa.accept_11_1_10_2_1_58 1
  21 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 145))))))))))))))))))))) (allB_succ
  20 145 (allA_of_3_1 20 20 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 19 145 (allA_succ_of_accept 18 19
  145 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 145 (accept_3_3 17 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 145 (Polychromatic418967fa.accept_20_15_19_5_1_7718 15 19 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 145 (accept_3_3 14 19 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 145 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 19
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 145
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 145 (accept_3_3 11 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 145 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 145 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 19 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 145 (accept_3_3 8 19 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 145 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 19 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 145 (accept_3_3 5 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  145 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 19 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 19 145 (Polychromatic418967fa.accept_23_3_19_7_1_7717 3 19 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 145 (accept_3_3 2 19 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 19 145 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 19 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 145))))))))))))))))))) (allB_succ 18 145 (allA_succ_of_accept 17
  18 145 (accept_3_3 17 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 18 145
  (Polychromatic418967fa.accept_7_2_4_5_1_313 16 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 18 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 18 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 18 145 (accept_3_3 14 18 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 18 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 18 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 18 145 (Polychromatic418967fa.accept_10_2_8_5_1_587
  12 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 18 145 (accept_3_3 11
  18 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 18 145
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 18 145 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 18 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 18 145 (accept_3_3 8 18 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 18 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 18 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 18 145 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 18 145 (accept_3_3 5 18 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 18 145 (Polychromatic418967fa.accept_13_4_5_2_1_1436 4
  18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 18 145
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 18 145 (accept_3_3 2 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 18
  145 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 18 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 145)))))))))))))))))) (allB_succ 17 145 (allA_of_3_1 17 17 145 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 16 145 (allA_succ_of_accept 15 16 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 16 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 16 145 (accept_3_3 14 16 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 16 145 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 16 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 16 145
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 16 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 16 145 (accept_3_3 11 16 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  16 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 16 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 16 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 16 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 16 145 (accept_3_3 8 16 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 16 145 (Polychromatic418967fa.accept_14_7_2_5_1_4528 7 16 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 16 145
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 16 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 16 145 (accept_3_3 5 16 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 16
  145 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 16 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 16 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 16 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 16 145 (accept_3_3 2 16 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 16 145 (Polychromatic418967fa.accept_10_1_6_5_1_304 1 16 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 16 145)))))))))))))))) (allB_succ 15 145 (allA_succ_of_accept 14 15
  145 (accept_3_3 14 15 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 15 145
  (Polychromatic418967fa.accept_7_6_1_5_1_322 13 15 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 15 145 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 15 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 15 145 (accept_3_3 11 15 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 15 145 5 2 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 15 145 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 15 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 145 (accept_3_3 8 15 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 145 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 15 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 15 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 15 145 5 1 3 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 15 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 15 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 15 145 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 15 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 145 (accept_3_3 2 15 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 145 (Polychromatic418967fa.accept_17_1_15_9_1_1743
  1 15 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 145))))))))))))))) (allB_succ 14
  145 (allA_of_3_1 14 14 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 13 145 (allA_succ_of_accept 12 13 145
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 13 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 13 145 (accept_3_3 11 13 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  13 145 (Polychromatic418967fa.accept_17_10_13_9_1_3913 10 13 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 13 145 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 13 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 145 (accept_3_3 8 13 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 145 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 13 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 145
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 13 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 145 (accept_3_3 5 13 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  145 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 13 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 13 145 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 13 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 145 (accept_3_3 2 13 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 13 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 13 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 145))))))))))))) (allB_succ 12 145 (allA_succ_of_accept 11 12
  145 (accept_3_3 11 12 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 12 145
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 12 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 12 145 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 12 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 12 145 (accept_3_3 8 12 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 12 145 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 12 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 12 145 (Polychromatic418967fa.accept_9_6_3_1_1_155 6
  12 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 12 145 (accept_3_3 5 12 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 12 145 (Polychromatic418967fa.accept_9_4_3_1_1_154 4
  12 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 12 145
  (Polychromatic418967fa.accept_10_3_2_5_1_295 3 12 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 12 145 (accept_3_3 2 12 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 12
  145 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 12 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 12 145)))))))))))) (allB_succ 11 145 (allA_of_3_1 11 11 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 10 145 (allA_succ_of_accept 9 10 145 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 10 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 10 145 (accept_3_3 8 10 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 10 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 10
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 10 145
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 6 10 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 10 145 5 1 2 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 10 145 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 10 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 10 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 10 145
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 10 145 (accept_3_3 2 10 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 10 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 10
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 10 145)))))))))) (allB_succ 9 145
  (allA_succ_of_accept 8 9 145 (accept_3_3 8 9 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 145
  (Polychromatic418967fa.accept_11_7_9_2_1_260 7 9 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 9 145 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 9 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 145 (accept_3_3 5 9 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 9 145 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 9 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 145 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 9
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 145 (accept_3_3 2 9 145
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 145 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 9
  145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 145))))))))) (allB_succ 8 145
  (allA_of_3_1 8 8 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 7 145 (allA_succ_of_accept 6 7 145
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 7 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 145 (accept_3_3 5 7 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 145
  (Polychromatic418967fa.accept_9_4_7_1_1_379 4 7 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 145 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 7 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 145 (accept_3_3 2 7 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 145 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 7 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 145))))))) (allB_succ 6 145 (allA_succ_of_accept 5 6 145
  (accept_3_3 5 6 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 6 145
  (Polychromatic418967fa.accept_7_4_6_5_1_141 4 6 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 6 145 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 6 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 6 145 (accept_3_3 2 6 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 6 145 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 6 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 145)))))) (allB_succ 5 145 (allA_of_3_1 5 5 145 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 4 145 (allA_succ_of_accept 3 4 145
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 4 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 4 145 (accept_3_3 2 4 145 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 4 145
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 4 145 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 4 145)))) (allB_succ 3 145 (allA_succ_of_accept 2 3 145 (accept_3_3 2 3 145 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 145 (Polychromatic418967fa.accept_7_1_3_5_1_33 1 3 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3 145))) (allB_succ 2 145 (allA_of_3_1 2 2 145 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_two
  145)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


